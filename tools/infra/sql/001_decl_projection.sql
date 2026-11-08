-- Promoted from scratch/ontology_pipeline_candidates/projection/001_decl_projection.sql
-- Owner: tools/infra/sql/001_decl_projection.sql (QMS-PLAN-PIPE-001 Phase 3.1)
-- Requires upstream public.catalog_database/catalog_schema/catalog_table/term.
-- Apply once under a separately authorized migration transaction. No DROP/repair.
BEGIN;
CREATE SCHEMA IF NOT EXISTS ig_decl_projection;

CREATE TABLE IF NOT EXISTS ig_decl_projection.source (
    deployment_uuid uuid NOT NULL,
    arango_database text NOT NULL CHECK (btrim(arango_database) <> ''),
    catalog_database_id text NOT NULL REFERENCES public.catalog_database(id) ON DELETE RESTRICT,
    PRIMARY KEY (deployment_uuid, arango_database),
    UNIQUE (catalog_database_id)
);

CREATE TABLE IF NOT EXISTS ig_decl_projection.generation (
    id uuid PRIMARY KEY,
    deployment_uuid uuid NOT NULL,
    arango_database text NOT NULL,
    generation_id text NOT NULL CHECK (generation_id ~ '^[A-Za-z0-9_]{1,32}$'),
    import_root text NOT NULL CHECK (btrim(import_root) <> ''),
    namespace text NOT NULL CHECK (btrim(namespace) <> ''),
    build_fingerprint text NOT NULL CHECK (build_fingerprint ~ '^[0-9a-f]{64}$'),
    receipt jsonb NOT NULL CHECK (jsonb_typeof(receipt) = 'object'),
    expected_declarations bigint NOT NULL CHECK (expected_declarations > 0),
    expected_edges bigint NOT NULL CHECK (expected_edges >= 0),
    digest_version text NOT NULL CHECK (digest_version = 'ig-decl-projection-v1'),
    expected_digest text NOT NULL CHECK (expected_digest ~ '^[0-9a-f]{64}$'),
    status text NOT NULL DEFAULT 'loading' CHECK (status IN ('loading', 'complete')),
    actual_digest text,
    created_at timestamptz NOT NULL DEFAULT now(),
    completed_at timestamptz,
    FOREIGN KEY (deployment_uuid, arango_database)
        REFERENCES ig_decl_projection.source ON DELETE RESTRICT,
    UNIQUE (deployment_uuid, arango_database, generation_id),
    UNIQUE (id, deployment_uuid, arango_database, import_root, namespace),
    CHECK ((status = 'loading' AND actual_digest IS NULL AND completed_at IS NULL)
        OR (status = 'complete' AND actual_digest = expected_digest
            AND actual_digest IS NOT NULL AND completed_at IS NOT NULL))
);

CREATE TABLE IF NOT EXISTS ig_decl_projection.declaration (
    generation uuid NOT NULL REFERENCES ig_decl_projection.generation(id) ON DELETE RESTRICT,
    decl_key text NOT NULL CHECK (decl_key <> ''),
    name text NOT NULL CHECK (name <> ''),
    module text NOT NULL CHECK (module <> ''),
    payload jsonb NOT NULL CHECK (jsonb_typeof(payload) = 'object'),
    term_id text NOT NULL REFERENCES public.term(id) ON DELETE RESTRICT,
    catalog_table_id text NOT NULL REFERENCES public.catalog_table(id) ON DELETE RESTRICT,
    PRIMARY KEY (generation, decl_key),
    UNIQUE (generation, name),
    UNIQUE (generation, term_id),
    CHECK ((payload ->> '_key') IS NOT DISTINCT FROM decl_key),
    CHECK ((payload ->> 'name') IS NOT DISTINCT FROM name),
    CHECK ((payload ->> 'module') IS NOT DISTINCT FROM module)
);

CREATE TABLE IF NOT EXISTS ig_decl_projection.dependency (
    generation uuid NOT NULL REFERENCES ig_decl_projection.generation(id) ON DELETE RESTRICT,
    edge_key text NOT NULL CHECK (edge_key <> ''),
    src_key text NOT NULL,
    dst_key text NOT NULL,
    kind text NOT NULL CHECK (kind IN ('type', 'value')),
    payload jsonb NOT NULL CHECK (jsonb_typeof(payload) = 'object'),
    PRIMARY KEY (generation, edge_key),
    UNIQUE (generation, src_key, dst_key, kind),
    FOREIGN KEY (generation, src_key)
        REFERENCES ig_decl_projection.declaration(generation, decl_key) ON DELETE RESTRICT,
    FOREIGN KEY (generation, dst_key)
        REFERENCES ig_decl_projection.declaration(generation, decl_key) ON DELETE RESTRICT,
    CHECK ((payload ->> '_key') IS NOT DISTINCT FROM edge_key),
    CHECK ((payload ->> 'kind') IS NOT DISTINCT FROM kind)
);
CREATE INDEX IF NOT EXISTS dependency_inbound ON ig_decl_projection.dependency(generation, dst_key);
CREATE INDEX IF NOT EXISTS dependency_outbound ON ig_decl_projection.dependency(generation, src_key);

CREATE TABLE IF NOT EXISTS ig_decl_projection.scope_selection (
    deployment_uuid uuid NOT NULL,
    arango_database text NOT NULL,
    import_root text NOT NULL,
    namespace text NOT NULL,
    selected_generation uuid,
    revision bigint NOT NULL DEFAULT 0 CHECK (revision >= 0),
    PRIMARY KEY (deployment_uuid, arango_database, import_root, namespace),
    FOREIGN KEY (deployment_uuid, arango_database)
        REFERENCES ig_decl_projection.source ON DELETE RESTRICT,
    FOREIGN KEY (selected_generation, deployment_uuid, arango_database, import_root, namespace)
        REFERENCES ig_decl_projection.generation
          (id, deployment_uuid, arango_database, import_root, namespace) ON DELETE RESTRICT,
    CHECK ((revision = 0 AND selected_generation IS NULL)
        OR (revision > 0 AND selected_generation IS NOT NULL))
);
CREATE TABLE IF NOT EXISTS ig_decl_projection.selection_history (
    deployment_uuid uuid NOT NULL,
    arango_database text NOT NULL,
    import_root text NOT NULL,
    namespace text NOT NULL,
    revision bigint NOT NULL CHECK (revision > 0),
    selected_generation uuid NOT NULL,
    previous_generation uuid REFERENCES ig_decl_projection.generation(id) ON DELETE RESTRICT,
    selected_at timestamptz NOT NULL DEFAULT now(),
    PRIMARY KEY (deployment_uuid, arango_database, import_root, namespace, revision),
    FOREIGN KEY (selected_generation, deployment_uuid, arango_database, import_root, namespace)
        REFERENCES ig_decl_projection.generation
          (id, deployment_uuid, arango_database, import_root, namespace) ON DELETE RESTRICT
);

CREATE OR REPLACE FUNCTION ig_decl_projection.reject_mutation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'immutable projection row: %', TG_TABLE_NAME;
END $$;

CREATE OR REPLACE FUNCTION ig_decl_projection.require_loading_insert() RETURNS trigger
LANGUAGE plpgsql AS $$
DECLARE state text;
BEGIN
    SELECT status INTO state FROM ig_decl_projection.generation
      WHERE id = NEW.generation FOR UPDATE;
    IF state IS DISTINCT FROM 'loading' THEN
        RAISE EXCEPTION 'generation is absent or not loading';
    END IF;
    RETURN NEW;
END $$;
CREATE TRIGGER declaration_loading BEFORE INSERT ON ig_decl_projection.declaration
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.require_loading_insert();
CREATE TRIGGER dependency_loading BEFORE INSERT ON ig_decl_projection.dependency
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.require_loading_insert();
CREATE TRIGGER declaration_immutable BEFORE UPDATE OR DELETE ON ig_decl_projection.declaration
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.reject_mutation();
CREATE TRIGGER dependency_immutable BEFORE UPDATE OR DELETE ON ig_decl_projection.dependency
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.reject_mutation();
CREATE TRIGGER source_immutable BEFORE UPDATE OR DELETE ON ig_decl_projection.source
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.reject_mutation();
CREATE TRIGGER history_immutable BEFORE UPDATE OR DELETE ON ig_decl_projection.selection_history
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.reject_mutation();

CREATE OR REPLACE FUNCTION ig_decl_projection.generation_transition() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF TG_OP = 'DELETE' THEN RAISE EXCEPTION 'generation deletion is prohibited'; END IF;
    IF OLD.status <> 'loading' OR NEW.status <> 'complete'
       OR (to_jsonb(OLD) - ARRAY['status','actual_digest','completed_at'])
          IS DISTINCT FROM
          (to_jsonb(NEW) - ARRAY['status','actual_digest','completed_at']) THEN
        RAISE EXCEPTION 'only loading -> complete may change a generation';
    END IF;
    RETURN NEW;
END $$;
CREATE TRIGGER generation_transition BEFORE UPDATE OR DELETE ON ig_decl_projection.generation
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.generation_transition();

CREATE OR REPLACE FUNCTION ig_decl_projection.selection_guard() RETURNS trigger
LANGUAGE plpgsql AS $$
DECLARE state text;
BEGIN
    IF TG_OP = 'DELETE' THEN RAISE EXCEPTION 'selection deletion is prohibited'; END IF;
    IF TG_OP = 'INSERT' THEN
        IF NEW.revision <> 0 OR NEW.selected_generation IS NOT NULL THEN
            RAISE EXCEPTION 'initialize selection empty';
        END IF;
        RETURN NEW;
    END IF;
    IF (NEW.deployment_uuid, NEW.arango_database, NEW.import_root, NEW.namespace)
       IS DISTINCT FROM (OLD.deployment_uuid, OLD.arango_database, OLD.import_root, OLD.namespace)
       OR NEW.revision <> OLD.revision + 1 THEN
        RAISE EXCEPTION 'selection identity is immutable; revision must advance once';
    END IF;
    SELECT status INTO state FROM ig_decl_projection.generation WHERE id = NEW.selected_generation;
    IF state IS DISTINCT FROM 'complete' THEN RAISE EXCEPTION 'selection requires complete generation'; END IF;
    INSERT INTO ig_decl_projection.selection_history
        (deployment_uuid, arango_database, import_root, namespace, revision,
         selected_generation, previous_generation)
    VALUES (NEW.deployment_uuid, NEW.arango_database, NEW.import_root, NEW.namespace,
            NEW.revision, NEW.selected_generation, OLD.selected_generation);
    RETURN NEW;
END $$;
CREATE TRIGGER selection_guard BEFORE INSERT OR UPDATE OR DELETE ON ig_decl_projection.scope_selection
    FOR EACH ROW EXECUTE FUNCTION ig_decl_projection.selection_guard();
COMMIT;
