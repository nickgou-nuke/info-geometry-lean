# Pauli Closure Debt Audit

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

- Authority: `ArangoDB (Primary Authoritative Lane)`
- Declarations Audited: `8387`
- Anchored: `7540`
- Unanchored (Closure Debt): `847`

## 🛑 Closure Debts (Unanchored Declarations)

| kind | name | location |
| --- | --- | --- |
| `theorem` | `test_add` | `lean/ast_export_test.lean:1` |
| `def` | `main` | `lean/scripts/find_convex_lemma.lean:7` |
| `theorem` | `iterate_add` | `lean/SelfReference/Dynamics.lean:17` |
| `def` | `trajectory` | `lean/SelfReference/Dynamics.lean:28` |
| `theorem` | `trajectory_fixed_point` | `lean/SelfReference/Dynamics.lean:36` |
| `def` | `loopStep` | `lean/SelfReference/Core.lean:44` |
| `def` | `iterateClosedLoop` | `lean/SelfReference/Core.lean:51` |
| `def` | `mandateAgent` | `lean/SelfReference/Mandate.lean:37` |
| `def` | `incrementer` | `lean/SelfReference/Counterexamples.lean:15` |
| `def` | `incrementerLoop` | `lean/SelfReference/Counterexamples.lean:22` |
| `def` | `mirror` | `lean/SelfReference/Counterexamples.lean:29` |
| `def` | `mirrorReflective` | `lean/SelfReference/Counterexamples.lean:36` |
| `def` | `memoryCell` | `lean/SelfReference/Counterexamples.lean:43` |
| `def` | `memoryCellPersistent` | `lean/SelfReference/Counterexamples.lean:53` |
| `def` | `agentFunctor` | `lean/SelfReference/Categorical.lean:23` |
| `def` | `inducedCoalgebra` | `lean/SelfReference/Categorical.lean:45` |
| `def` | `main` | `lean/Docs/AutoTag.lean:26` |
| `def` | `main` | `lean/Docs/AutoTag.lean:46` |
| `def` | `autoBlueprints` | `lean/Docs/auto_blueprints.lean:10` |
| `def` | `generatedBlueprints` | `lean/Docs/generated_blueprints.lean:10` |
| `def` | `escapeLatex` | `lean/Docs/emit_blueprint_tex.lean:18` |
| `def` | `emitSkeletonNode` | `lean/Docs/emit_blueprint_tex.lean:22` |
| `def` | `emitBlueprint` | `lean/Docs/emit_blueprint_tex.lean:50` |
| `def` | `emit_blueprint_main` | `lean/Docs/emit_blueprint_tex.lean:84` |
| `def` | `main` | `lean/Docs/emit_blueprint_tex.lean:95` |
| `def` | `collectNames` | `lean/DAG/SearchCore.lean:8` |
| `def` | `containsCI` | `lean/DAG/SearchCore.lean:16` |
| `def` | `queryContains` | `lean/DAG/SearchCore.lean:20` |
| `def` | `queryContainsCI` | `lean/DAG/SearchCore.lean:29` |
| `def` | `queryContainsWithCount` | `lean/DAG/SearchCore.lean:38` |
| `def` | `double` | `lean/DAG/ExactMorphismTest.lean:29` |
| `def` | `triple` | `lean/DAG/ExactMorphismTest.lean:32` |
| `def` | `sextuple` | `lean/DAG/ExactMorphismTest.lean:35` |
| `def` | `addTwo` | `lean/DAG/ExactMorphismTest.lean:38` |
| `def` | `makeZero` | `lean/DAG/ExactMorphismTest.lean:41` |
| `def` | `myId` | `lean/DAG/ExactMorphismTest.lean:44` |
| `def` | `succ'` | `lean/DAG/ExactMorphismTest.lean:47` |
| `def` | `flipBool` | `lean/DAG/ExactMorphismTest.lean:55` |
| `def` | `polyId` | `lean/DAG/ExactMorphismTest.lean:60` |
| `def` | `dottedName` | `lean/DAG/ExportDecls.lean:56` |
| `def` | `normalizePrefix` | `lean/DAG/ExportDecls.lean:60` |
| `def` | `inNamespace` | `lean/DAG/ExportDecls.lean:63` |
| `def` | `kindString` | `lean/DAG/ExportDecls.lean:71` |
| `def` | `moduleNameFor` | `lean/DAG/ExportDecls.lean:81` |
| `def` | `dedupNames` | `lean/DAG/ExportDecls.lean:96` |
| `def` | `sortStrings` | `lean/DAG/ExportDecls.lean:99` |
| `def` | `keepDep` | `lean/DAG/ExportDecls.lean:102` |
| `def` | `getDeps` | `lean/DAG/ExportDecls.lean:112` |
| `def` | `shouldInclude` | `lean/DAG/ExportDecls.lean:123` |
| `def` | `getDocString` | `lean/DAG/ExportDecls.lean:128` |
| `def` | `collectDecls` | `lean/DAG/ExportDecls.lean:133` |
| `def` | `writeOutput` | `lean/DAG/ExportDecls.lean:158` |
| `def` | `firstSegment` | `lean/DAG/ExportDecls.lean:183` |
| `def` | `sampleNames` | `lean/DAG/ExportDecls.lean:188` |
| `def` | `runExport` | `lean/DAG/ExportDecls.lean:197` |
| `def` | `main` | `lean/DAG/ExportDecls.lean:234` |
| `def` | `sampleNames` | `lean/DAG/SearchCoreTests.lean:7` |
| `def` | `MorphismState` | `lean/DAG/ExactMorphism.lean:106` |
| `def` | `getMorphismState` | `lean/DAG/ExactMorphism.lean:127` |
| `def` | `withUnaryMorphismSignature` | `lean/DAG/ExactMorphism.lean:147` |
| `def` | `withMorphismSignature` | `lean/DAG/ExactMorphism.lean:174` |
| `def` | `headNameOf` | `lean/DAG/ExactMorphism.lean:200` |
| `def` | `mkMorphismEntry` | `lean/DAG/ExactMorphism.lean:215` |
| `def` | `mkUnaryMorphismApp` | `lean/DAG/ExactMorphism.lean:232` |
| `def` | `MorphismEntry` | `lean/DAG/ExactMorphism.lean:245` |
| `def` | `harvestMorphisms` | `lean/DAG/ExactMorphism.lean:274` |
| `def` | `indexMorphismCache` | `lean/DAG/ExactMorphism.lean:301` |
| `def` | `checkCommutativityExact` | `lean/DAG/ExactMorphism.lean:353` |
| `def` | `findCommutativeSquaresFromHarvest` | `lean/DAG/ExactMorphism.lean:394` |
| `def` | `findCommutativeSquaresExact` | `lean/DAG/ExactMorphism.lean:434` |
| `def` | `findSpanCandidates` | `lean/DAG/ExactMorphism.lean:462` |
| `def` | `findCospanCandidates` | `lean/DAG/ExactMorphism.lean:484` |
| `def` | `checkDefinitionalInverse` | `lean/DAG/ExactMorphism.lean:512` |
| `def` | `findDefinitionalInverses` | `lean/DAG/ExactMorphism.lean:541` |
| `def` | `runExactPipeline` | `lean/DAG/ExactMorphism.lean:569` |
| `def` | `printExactPipelineSummary` | `lean/DAG/ExactMorphism.lean:587` |
| `def` | `elabFindMorphisms` | `lean/DAG/ExactMorphism.lean:604` |
| `def` | `elabFindSquares` | `lean/DAG/ExactMorphism.lean:623` |
| `def` | `elabIndexMorphisms` | `lean/DAG/ExactMorphism.lean:646` |
| `def` | `main` | `lean/DAG/ExprArangoExport.lean:413` |
| `def` | `main` | `lean/DAG/ExprArangoExport.lean:437` |
| `def` | `QueryM` | `lean/DAG/QueryEngine.lean:11` |
| `def` | `getEnv` | `lean/DAG/QueryEngine.lean:19` |
| `def` | `matchDeclaration` | `lean/DAG/QueryEngine.lean:21` |
| `def` | `where_` | `lean/DAG/QueryEngine.lean:24` |
| `def` | `followChirality` | `lean/DAG/QueryEngine.lean:29` |
| `def` | `stepExpr` | `lean/DAG/QueryEngine.lean:35` |
| `def` | `buildTwoComplex` | `lean/DAG/TwoComplex.lean:16` |
| `def` | `boundary1` | `lean/DAG/TwoComplex.lean:52` |
| `def` | `boundary2` | `lean/DAG/TwoComplex.lean:64` |
| `def` | `matMul` | `lean/DAG/TwoComplex.lean:86` |
| `def` | `boundarySquaredZero` | `lean/DAG/TwoComplex.lean:102` |
| `def` | `eulerCharacteristic` | `lean/DAG/TwoComplex.lean:108` |
| `def` | `redundancySupport` | `lean/DAG/TwoComplex.lean:114` |
| `def` | `gaussianRank` | `lean/DAG/TwoComplex.lean:118` |
| `def` | `betti1` | `lean/DAG/TwoComplex.lean:145` |
| `def` | `searchEnv` | `lean/DAG/FinalSearch.lean:12` |
| `def` | `compositionHeadsCompatible` | `lean/DAG/CategoryBridge.lean:75` |
| `def` | `isCompositionExact` | `lean/DAG/CategoryBridge.lean:87` |
| `def` | `isDefinitionalIdentity` | `lean/DAG/CategoryBridge.lean:107` |
| `def` | `verifyCompositionalWitness` | `lean/DAG/CategoryBridge.lean:181` |
| `def` | `printCompositionalBridgeVerdict` | `lean/DAG/CategoryBridge.lean:259` |
| `def` | `double` | `lean/DAG/CategoryBridgeTest.lean:22` |
| `def` | `triple` | `lean/DAG/CategoryBridgeTest.lean:23` |
| `def` | `sextuple` | `lean/DAG/CategoryBridgeTest.lean:24` |
| `def` | `myId` | `lean/DAG/CategoryBridgeTest.lean:25` |
| `def` | `succ'` | `lean/DAG/CategoryBridgeTest.lean:26` |
| `def` | `fXY` | `lean/DAG/CategoryBridgeTest.lean:30` |
| `def` | `gYZ` | `lean/DAG/CategoryBridgeTest.lean:31` |
| `def` | `compXZ` | `lean/DAG/CategoryBridgeTest.lean:32` |
| `def` | `mkE` | `lean/DAG/CategoryBridgeTest.lean:35` |
| `def` | `runBridgeTest` | `lean/DAG/CategoryBridgeTest.lean:46` |
| `def` | `writeOutput` | `lean/DAG/SkeletonExport.lean:16` |
| `def` | `main` | `lean/DAG/SkeletonExport.lean:28` |
| `def` | `main` | `lean/DAG/RepresentationDepthExport.lean:254` |
| `def` | `main` | `lean/DAG/RepresentationDepthExport.lean:265` |
| `def` | `tarjan` | `lean/DAG/SCC.lean:85` |
| `def` | `extractNamedMorphismSignature` | `lean/DAG/Functor.lean:43` |
| `def` | `extractMorphismSignature` | `lean/DAG/Functor.lean:54` |
| `def` | `recognizeMorphismShallow` | `lean/DAG/Functor.lean:58` |
| `def` | `getAllMorphismsWithDiagnostics` | `lean/DAG/Functor.lean:84` |
| `def` | `getAllMorphisms` | `lean/DAG/Functor.lean:110` |
| `def` | `findCommutativeSquares` | `lean/DAG/Functor.lean:124` |
| `def` | `schema` | `lean/DAG/RawInfoTreeExport.lean:233` |
| `def` | `stage` | `lean/DAG/RawInfoTreeExport.lean:234` |
| `def` | `mkKey` | `lean/DAG/RawInfoTreeExport.lean:236` |
| `def` | `pushAll` | `lean/DAG/RawInfoTreeExport.lean:239` |
| `def` | `sanitize` | `lean/DAG/RawInfoTreeExport.lean:242` |
| `def` | `writeJsonl` | `lean/DAG/RawInfoTreeExport.lean:246` |
| `def` | `syntaxText` | `lean/DAG/RawInfoTreeExport.lean:255` |
| `def` | `exprProjection` | `lean/DAG/RawInfoTreeExport.lean:258` |
| `def` | `constNamesOfExpr` | `lean/DAG/RawInfoTreeExport.lean:261` |
| `def` | `optionExprText` | `lean/DAG/RawInfoTreeExport.lean:264` |
| `def` | `constNamesOfOptionExpr` | `lean/DAG/RawInfoTreeExport.lean:269` |
| `def` | `payloadText` | `lean/DAG/RawInfoTreeExport.lean:274` |
| `def` | `fileMapPositionsText` | `lean/DAG/RawInfoTreeExport.lean:277` |
| `def` | `optionsRows` | `lean/DAG/RawInfoTreeExport.lean:280` |
| `def` | `optionsText` | `lean/DAG/RawInfoTreeExport.lean:286` |
| `def` | `importNamesText` | `lean/DAG/RawInfoTreeExport.lean:289` |
| `def` | `moduleNamesText` | `lean/DAG/RawInfoTreeExport.lean:292` |
| `def` | `stableHash` | `lean/DAG/RawInfoTreeExport.lean:295` |
| `def` | `mvarIdText` | `lean/DAG/RawInfoTreeExport.lean:299` |
| `def` | `fvarIdText` | `lean/DAG/RawInfoTreeExport.lean:302` |
| `def` | `envRefRow` | `lean/DAG/RawInfoTreeExport.lean:305` |
| `def` | `mctxRefRow` | `lean/DAG/RawInfoTreeExport.lean:349` |
| `def` | `mctxDeclRows` | `lean/DAG/RawInfoTreeExport.lean:382` |
| `def` | `mctxSignature` | `lean/DAG/RawInfoTreeExport.lean:424` |
| `def` | `emitMctxRefAndDecls` | `lean/DAG/RawInfoTreeExport.lean:460` |
| `def` | `lctxDeclRows` | `lean/DAG/RawInfoTreeExport.lean:481` |
| `def` | `lctxSignature` | `lean/DAG/RawInfoTreeExport.lean:529` |
| `def` | `emitLctxRef` | `lean/DAG/RawInfoTreeExport.lean:541` |
| `def` | `emitMctxDeclLctxRefs` | `lean/DAG/RawInfoTreeExport.lean:574` |
| `def` | `exprGraphLeakage` | `lean/DAG/RawInfoTreeExport.lean:585` |
| `def` | `lctxLeakage` | `lean/DAG/RawInfoTreeExport.lean:588` |
| `def` | `syntaxLeakage` | `lean/DAG/RawInfoTreeExport.lean:591` |
| `def` | `termInfoLeakage` | `lean/DAG/RawInfoTreeExport.lean:594` |
| `def` | `contextRowAndLeakage` | `lean/DAG/RawInfoTreeExport.lean:600` |
| `def` | `optionNameText` | `lean/DAG/RawInfoTreeExport.lean:691` |
| `def` | `optionNameDecls` | `lean/DAG/RawInfoTreeExport.lean:696` |
| `def` | `completionPayload` | `lean/DAG/RawInfoTreeExport.lean:701` |
| `def` | `emitCompletionLctxRefs` | `lean/DAG/RawInfoTreeExport.lean:765` |
| `def` | `emitInfoLctxRefs` | `lean/DAG/RawInfoTreeExport.lean:783` |
| `def` | `emitInfoMctxRefsAndDecls` | `lean/DAG/RawInfoTreeExport.lean:805` |
| `def` | `emitInfoMctxLctxRefs` | `lean/DAG/RawInfoTreeExport.lean:818` |
| `def` | `infoKindAndPayload` | `lean/DAG/RawInfoTreeExport.lean:833` |
| `def` | `exportFile` | `lean/DAG/RawInfoTreeExport.lean:1110` |
| `def` | `main` | `lean/DAG/RawInfoTreeExport.lean:1183` |
| `def` | `main` | `lean/DAG/RawInfoTreeExport.lean:1192` |
| `def` | `hydrate` | `lean/DAG/Hydrate.lean:8` |
| `def` | `mkE` | `lean/DAG/IntegrationTest.lean:21` |
| `def` | `runBridgeTest` | `lean/DAG/IntegrationTest.lean:31` |
| `def` | `matTranspose` | `lean/DAG/GraphHodge.lean:34` |
| `def` | `matAdd` | `lean/DAG/GraphHodge.lean:46` |
| `def` | `matDiag` | `lean/DAG/GraphHodge.lean:56` |
| `def` | `matTrace` | `lean/DAG/GraphHodge.lean:60` |
| `def` | `matIdentity` | `lean/DAG/GraphHodge.lean:64` |
| `def` | `coboundary0` | `lean/DAG/GraphHodge.lean:76` |
| `def` | `coboundary1` | `lean/DAG/GraphHodge.lean:80` |
| `def` | `laplacian0` | `lean/DAG/GraphHodge.lean:89` |
| `def` | `laplacian1` | `lean/DAG/GraphHodge.lean:96` |
| `def` | `betti0` | `lean/DAG/GraphHodge.lean:110` |
| `def` | `betti1Hodge` | `lean/DAG/GraphHodge.lean:119` |
| `def` | `ChiralGrading` | `lean/DAG/GraphHodge.lean:136` |
| `def` | `chiralGradingFromDepths` | `lean/DAG/GraphHodge.lean:141` |
| `def` | `chiralDiagMatrix` | `lean/DAG/GraphHodge.lean:146` |
| `def` | `graphDirac` | `lean/DAG/GraphHodge.lean:164` |
| `def` | `extendedChiralGrading` | `lean/DAG/GraphHodge.lean:195` |
| `def` | `chiralAnticommutes` | `lean/DAG/GraphHodge.lean:215` |
| `def` | `hodgeSummary` | `lean/DAG/GraphHodge.lean:242` |
| `def` | `computeInitialLabel` | `lean/DAG/Isomorphism.lean:18` |
| `def` | `wlRound` | `lean/DAG/Isomorphism.lean:25` |
| `def` | `computeStructuralHash` | `lean/DAG/Isomorphism.lean:55` |
| `def` | `compareSymmetry` | `lean/DAG/Isomorphism.lean:70` |
| `def` | `main` | `lean/DAG/FindFinrank.lean:7` |
| `def` | `main` | `lean/DAG/ProcessFlowExport.lean:890` |
| `def` | `main` | `lean/DAG/ProcessFlowExport.lean:901` |
| `def` | `componentPathCountsAlong` | `lean/DAG/Analysis.lean:9` |
| `def` | `componentPathCounts` | `lean/DAG/Analysis.lean:31` |
| `def` | `componentPathCountsUpward` | `lean/DAG/Analysis.lean:39` |
| `def` | `pathCountFrom` | `lean/DAG/Analysis.lean:47` |
| `def` | `distanceMap` | `lean/DAG/Analysis.lean:94` |
| `def` | `influenceFrom` | `lean/DAG/Analysis.lean:119` |
| `def` | `vulnerabilityOf` | `lean/DAG/Analysis.lean:134` |
| `def` | `rootSet` | `lean/DAG/Analysis.lean:177` |
| `def` | `capstoneSet` | `lean/DAG/Analysis.lean:188` |
| `def` | `depthMinFromRoots` | `lean/DAG/Analysis.lean:199` |
| `def` | `depthMaxFromRoots` | `lean/DAG/Analysis.lean:256` |
| `def` | `topologicalLayersFromRoots` | `lean/DAG/Analysis.lean:262` |
| `def` | `depthSpreadFromRoots` | `lean/DAG/Analysis.lean:284` |
| `def` | `rootContributionCounts` | `lean/DAG/Analysis.lean:299` |
| `def` | `deepestRootChains` | `lean/DAG/Analysis.lean:315` |
| `def` | `componentRepresentative` | `lean/DAG/Analysis.lean:341` |
| `def` | `extractTheorySkeletonWithPreferred` | `lean/DAG/Analysis.lean:420` |
| `def` | `extractTheorySkeleton` | `lean/DAG/Analysis.lean:430` |
| `def` | `searchEnv` | `lean/DAG/Search.lean:176` |
| `def` | `searchEnvMany` | `lean/DAG/Search.lean:182` |
| `def` | `collectExprConsts` | `lean/DAG/Basic.lean:56` |
| `def` | `edgesFromConstantInfo` | `lean/DAG/Basic.lean:63` |
| `def` | `buildGraphFromEnv` | `lean/DAG/Basic.lean:79` |
| `def` | `graphToForwardJson` | `lean/DAG/ExportForwardGraph.lean:32` |
| `def` | `parseImports` | `lean/DAG/ExportForwardGraph.lean:44` |
| `def` | `main` | `lean/DAG/ExportForwardGraph.lean:53` |
| `def` | `addNode` | `lean/DAG/Disassembler.lean:28` |
| `def` | `addEdge` | `lean/DAG/Disassembler.lean:35` |
| `def` | `disassembleExpr` | `lean/DAG/Disassembler.lean:97` |
| `def` | `disassembleConst` | `lean/DAG/Disassembler.lean:101` |
| `def` | `liftNaturalityNormalizationLemmas` | `lean/DAG/LiftNaturality.lean:13` |
| `def` | `taggedLiftDecls` | `lean/DAG/LiftNaturality.lean:19` |
| `def` | `LiftSeed` | `lean/DAG/LiftNaturality.lean:52` |
| `def` | `collectLiftSeeds` | `lean/DAG/LiftNaturality.lean:130` |
| `def` | `topo` | `lean/DAG/Topo.lean:3` |
| `def` | `searchEnv` | `lean/DAG/SearchRank.lean:17` |
| `def` | `searchEnvMany` | `lean/DAG/SearchRank.lean:23` |
| `def` | `buildStructuralPayload` | `lean/DAG/StructuralExport.lean:309` |
| `def` | `writeStructuralJsonOutput` | `lean/DAG/StructuralExport.lean:352` |
| `def` | `isContextText` | `lean/DAG/ServerExport.lean:60` |
| `def` | `exportFromSnaps` | `lean/DAG/ServerExport.lean:74` |
| `def` | `semanticBlocksPayload` | `lean/DAG/ServerExport.lean:321` |
| `def` | `semanticBlocks` | `lean/DAG/ServerExport.lean:360` |
| `def` | `getTargets` | `lean/DAG/ServerExport.lean:368` |
| `def` | `sliceFor` | `lean/DAG/ServerExport.lean:386` |
| `def` | `renderSlice` | `lean/DAG/ServerExport.lean:418` |
| `def` | `impact` | `lean/DAG/Impact.lean:9` |
| `def` | `reverseImpact` | `lean/DAG/Impact.lean:31` |
| `def` | `main` | `lean/DAG/RootOrderExport.lean:182` |
| `def` | `nextNodeId` | `lean/DAG/GlobalDisassembler.lean:28` |
| `def` | `nextDeclId` | `lean/DAG/GlobalDisassembler.lean:33` |
| `def` | `writeNode` | `lean/DAG/GlobalDisassembler.lean:38` |
| `def` | `writeEdge` | `lean/DAG/GlobalDisassembler.lean:44` |
| `def` | `writeDecl` | `lean/DAG/GlobalDisassembler.lean:48` |
| `def` | `processEnvironment` | `lean/DAG/GlobalDisassembler.lean:111` |
| `def` | `globalDisassemblerMain` | `lean/DAG/GlobalDisassembler.lean:139` |
| `def` | `arrayReplicate` | `lean/DAG/Util.lean:6` |
| `def` | `collectDeps` | `lean/DAG/Util.lean:11` |
| `def` | `isFromMainModule` | `lean/DAG/Util.lean:26` |
| `def` | `leafNameString` | `lean/DAG/Util.lean:35` |
| `def` | `containsPrivateMarker` | `lean/DAG/Util.lean:40` |
| `def` | `isGeneratedOrUnstableName` | `lean/DAG/Util.lean:43` |
| `def` | `dominators` | `lean/DAG/Dominators.lean:26` |
| `def` | `aggregateTelemetry` | `lean/DAG/HolonomyExporter.lean:39` |
| `def` | `processFile` | `lean/DAG/HolonomyExporter.lean:67` |
| `def` | `holonomyExporterMain` | `lean/DAG/HolonomyExporter.lean:126` |
| `def` | `main` | `lean/DAG/HolonomyExporter.lean:138` |
| `def` | `computeExprHomology` | `lean/DAG/Betti.lean:14` |
| `def` | `commutativeSquare` | `lean/DAG/SubgraphMatch.lean:38` |
| `def` | `span` | `lean/DAG/SubgraphMatch.lean:44` |
| `def` | `cospan` | `lean/DAG/SubgraphMatch.lean:50` |
| `def` | `diamond` | `lean/DAG/SubgraphMatch.lean:56` |
| `def` | `triangle` | `lean/DAG/SubgraphMatch.lean:62` |
| `def` | `fork` | `lean/DAG/SubgraphMatch.lean:68` |
| `def` | `buildDeclAdjacency` | `lean/DAG/SubgraphMatch.lean:92` |
| `def` | `DeclAdjacency` | `lean/DAG/SubgraphMatch.lean:98` |
| `def` | `findMotifMatches` | `lean/DAG/SubgraphMatch.lean:233` |
| `def` | `printMotifMatches` | `lean/DAG/SubgraphMatch.lean:242` |
| `def` | `produces` | `lean/DAG/BlockExport.lean:68` |
| `def` | `mkStableBlockId` | `lean/DAG/BlockExport.lean:74` |
| `def` | `classifyProducedDecls` | `lean/DAG/BlockExport.lean:78` |
| `def` | `primaryDeclSet` | `lean/DAG/BlockExport.lean:89` |
| `def` | `collectPrimarySpineTags` | `lean/DAG/BlockExport.lean:98` |
| `def` | `collectPrimaryDeps` | `lean/DAG/BlockExport.lean:103` |
| `def` | `summarizeSpineTags` | `lean/DAG/BlockExport.lean:119` |
| `def` | `collectInfoDeps` | `lean/DAG/BlockExport.lean:240` |
| `def` | `buildGraphFromEnvOn` | `lean/DAG/BlockExport.lean:290` |
| `def` | `producerMap` | `lean/DAG/BlockExport.lean:311` |
| `def` | `buildBlockGraph` | `lean/DAG/BlockExport.lean:320` |
| `def` | `minimalBlocksFor` | `lean/DAG/BlockExport.lean:344` |
| `def` | `exportFile` | `lean/DAG/BlockExport.lean:375` |
| `def` | `isScopeDeclBlock` | `lean/DAG/BlockExport.lean:530` |
| `def` | `isAmbientBlock` | `lean/DAG/BlockExport.lean:536` |
| `def` | `minimalBlocksWithContext` | `lean/DAG/BlockExport.lean:549` |
| `def` | `renderIndices` | `lean/DAG/BlockExport.lean:560` |
| `def` | `sliceToString` | `lean/DAG/BlockExport.lean:604` |
| `def` | `emitQuiver` | `lean/DAG/BlockExport.lean:608` |
| `def` | `escapeLeanString` | `lean/DAG/BlockExport.lean:658` |
| `def` | `emitTacticQuiver` | `lean/DAG/BlockExport.lean:666` |
| `def` | `blockExportMain` | `lean/DAG/BlockExport.lean:713` |
| `def` | `indexerSchemaVersion` | `lean/DAG/Indexer.lean:89` |
| `def` | `parseImports` | `lean/DAG/Indexer.lean:117` |
| `def` | `getKindString` | `lean/DAG/Indexer.lean:126` |
| `def` | `getModuleName` | `lean/DAG/Indexer.lean:137` |
| `def` | `moduleToLeanFile` | `lean/DAG/Indexer.lean:142` |
| `def` | `recognizeMorphism` | `lean/DAG/Indexer.lean:153` |
| `def` | `addEdge` | `lean/DAG/Indexer.lean:171` |
| `def` | `processConstant` | `lean/DAG/Indexer.lean:193` |
| `def` | `runIndexer` | `lean/DAG/Indexer.lean:430` |
| `def` | `indexerMain` | `lean/DAG/Indexer.lean:541` |
| `def` | `main` | `lean/DAG/Indexer.lean:568` |
| `def` | `getProofState` | `lean/Agent/ProofStateExport.lean:30` |
| `def` | `getGoalTargets` | `lean/Agent/ProofStateExport.lean:57` |
| `def` | `getEnvFingerprint` | `lean/Agent/ProofStateExport.lean:92` |
| `def` | `checkSnippet` | `lean/Agent/ProofStateExport.lean:118` |
| `def` | `getDeclValue` | `lean/Agent/ProofStateExport.lean:161` |
| `def` | `validateDecl` | `lean/Agent/ProofStateExport.lean:193` |
| `def` | `bridgeVersion` | `lean/Agent/Protocol.lean:13` |
| `def` | `BridgeVersion` | `lean/Agent/Protocol.lean:41` |
| `def` | `sessionIdOfDoc` | `lean/Agent/CompilerBridgeCore.lean:32` |
| `def` | `envFingerprintOfDoc` | `lean/Agent/CompilerBridgeCore.lean:108` |
| `def` | `responseMetaOfDoc` | `lean/Agent/CompilerBridgeCore.lean:120` |
| `def` | `mkCompilerError` | `lean/Agent/CompilerBridgeCore.lean:128` |
| `def` | `unsupportedProtocolVersionError` | `lean/Agent/CompilerBridgeCore.lean:148` |
| `def` | `validateVersion` | `lean/Agent/CompilerBridgeCore.lean:156` |
| `def` | `severityOfDiagnostic` | `lean/Agent/CompilerBridgeCore.lean:161` |
| `def` | `headMetaOfText` | `lean/Agent/CompilerBridgeCore.lean:270` |
| `def` | `exprFingerprintOfText` | `lean/Agent/CompilerBridgeCore.lean:367` |
| `def` | `headFingerprintOfExpr` | `lean/Agent/CompilerBridgeCore.lean:370` |
| `def` | `headMetaOfExpr` | `lean/Agent/CompilerBridgeCore.lean:373` |
| `def` | `exprFingerprintOfExpr` | `lean/Agent/CompilerBridgeCore.lean:378` |
| `def` | `compilerErrorOfDiagnostic` | `lean/Agent/CompilerBridgeCore.lean:526` |
| `def` | `docDiagnostics` | `lean/Agent/CompilerBridgeCore.lean:542` |
| `def` | `diagnosticsOk` | `lean/Agent/CompilerBridgeCore.lean:546` |
| `def` | `mkDocError` | `lean/Agent/CompilerBridgeCore.lean:549` |
| `def` | `proofStateTaskAt` | `lean/Agent/CompilerBridgeCore.lean:631` |
| `def` | `finalSnapshotTask` | `lean/Agent/CompilerBridgeCore.lean:651` |
| `def` | `snapshotTaskAt` | `lean/Agent/CompilerBridgeCore.lean:663` |
| `def` | `ppExprAtSnapshot` | `lean/Agent/CompilerBridgeCore.lean:671` |
| `def` | `findDeclInfo` | `lean/Agent/CompilerBridgeCore.lean:675` |
| `def` | `constantHasSorry` | `lean/Agent/CompilerBridgeCore.lean:687` |
| `def` | `declarationNotFoundError` | `lean/Agent/CompilerBridgeCore.lean:693` |
| `def` | `containsSorryError` | `lean/Agent/CompilerBridgeCore.lean:700` |
| `lemma` | `DualFlatPotential` | `lean/InfoGeometry/Fenchel.lean:141` |
| `lemma` | `DualFlatPotential` | `lean/InfoGeometry/Fenchel.lean:148` |
| `def` | `collectSoftEvidence` | `lean/InfoGeometry/AuditStrict.lean:14` |
| `def` | `main` | `lean/scripts/DAG/Exploration/NaturalityPromoter.lean:205` |
| `def` | `findRecursiveTheorems` | `lean/scripts/DAG/Exploration/QueryEngine.lean:15` |
| `def` | `main` | `lean/scripts/DAG/Exploration/QueryEngine.lean:42` |
| `def` | `main` | `lean/scripts/DAG/Exploration/FinalSearch.lean:31` |
| `def` | `main` | `lean/scripts/DAG/Exploration/NaturalityDiagnostics.lean:167` |
| `def` | `main` | `lean/scripts/DAG/Exploration/CompilerBridgeServer.lean:7` |
| `def` | `main` | `lean/scripts/DAG/Exploration/SquarePromoter.lean:87` |
| `def` | `main` | `lean/scripts/DAG/Exploration/Functor.lean:86` |
| `def` | `main` | `lean/scripts/DAG/Exploration/SemanticBlockServer.lean:6` |
| `def` | `main` | `lean/scripts/DAG/Exploration/Isomorphism.lean:31` |
| `def` | `runEnvScript` | `lean/scripts/DAG/Exploration/Common.lean:8` |
| `def` | `runMetaScript` | `lean/scripts/DAG/Exploration/Common.lean:13` |
| `def` | `main` | `lean/scripts/DAG/Exploration/Search.lean:31` |
| `def` | `main` | `lean/scripts/DAG/Exploration/Disassembler.lean:26` |
| `def` | `main` | `lean/scripts/DAG/Exploration/SearchRank.lean:29` |
| `def` | `main` | `lean/scripts/DAG/Exploration/FunctorDiagnostics.lean:54` |
| `def` | `main` | `lean/scripts/DAG/Exploration/SemanticBlockExport.lean:276` |
| `def` | `main` | `lean/scripts/DAG/Exploration/HarvestDiagnostics.lean:100` |
| `def` | `main` | `lean/scripts/DAG/Exploration/SemanticSnapshotServer.lean:8` |
| `def` | `main` | `lean/scripts/DAG/Exploration/LiftNaturalityDiagnostics.lean:79` |
| `def` | `main` | `lean/scripts/DAG/Exploration/Betti.lean:25` |
| `def` | `classifyProofShape` | `lean/InfoGeometry/Lint/Vacuity.lean:68` |
| `def` | `ProofShape` | `lean/InfoGeometry/Lint/Vacuity.lean:109` |
| `def` | `ProofShape` | `lean/InfoGeometry/Lint/Vacuity.lean:117` |
| `def` | `classifyStatementShape` | `lean/InfoGeometry/Lint/Vacuity.lean:139` |
| `def` | `hasRoleTag` | `lean/InfoGeometry/Lint/Vacuity.lean:166` |
| `def` | `isExempt` | `lean/InfoGeometry/Lint/Vacuity.lean:170` |
| `def` | `containsCertifiedMarker` | `lean/InfoGeometry/Lint/Vacuity.lean:174` |
| `def` | `declNameLeaf` | `lean/InfoGeometry/Lint/Vacuity.lean:178` |
| `def` | `eraseCertifiedMarker` | `lean/InfoGeometry/Lint/Vacuity.lean:184` |
| `def` | `eraseCertifiedMarkerLeaf` | `lean/InfoGeometry/Lint/Vacuity.lean:188` |
| `def` | `isCertifiedTransportName` | `lean/InfoGeometry/Lint/Vacuity.lean:192` |
| `def` | `isCertifiedTwinForward` | `lean/InfoGeometry/Lint/Vacuity.lean:209` |
| `def` | `lintDecl` | `lean/InfoGeometry/Lint/Vacuity.lean:218` |
| `def` | `elabVacuityLint` | `lean/InfoGeometry/Lint/Vacuity.lean:282` |
| `def` | `elabVacuityLintFile` | `lean/InfoGeometry/Lint/Vacuity.lean:298` |
| `def` | `elabVacuityLintDecl` | `lean/InfoGeometry/Lint/Vacuity.lean:317` |
| `theorem` | `unruhFlow_is_modular_flow` | `lean/InfoGeometry/Dynamics/UnruhKMS.lean:108` |
| `def` | `isComplexStructureOp` | `lean/InfoGeometry/Krein/Prelude.lean:27` |
| `lemma` | `complex_i_sq_neg_id` | `lean/InfoGeometry/Krein/Prelude.lean:30` |
| `lemma` | `complex_i_isComplexStructureOp` | `lean/InfoGeometry/Krein/Prelude.lean:35` |
| `lemma` | `chiralityProjPlus_idempotent` | `lean/InfoGeometry/Krein/Prelude.lean:61` |
| `lemma` | `chiralityProjMinus_idempotent` | `lean/InfoGeometry/Krein/Prelude.lean:66` |
| `lemma` | `chiralityProjPlus_comp_chiralityProjMinus` | `lean/InfoGeometry/Krein/Prelude.lean:71` |
| `lemma` | `chiralityProjMinus_comp_chiralityProjPlus` | `lean/InfoGeometry/Krein/Prelude.lean:79` |
| `lemma` | `chiralityProjPlus_add_chiralityProjMinus` | `lean/InfoGeometry/Krein/Prelude.lean:87` |
| `lemma` | `neg_complex_i_isComplexStructureOp` | `lean/InfoGeometry/Krein/Prelude.lean:93` |
| `theorem` | `vacuumChoice_switch_swaps_splits_plus` | `lean/InfoGeometry/Krein/Prelude.lean:141` |
| `theorem` | `vacuumChoice_switch_swaps_splits_minus` | `lean/InfoGeometry/Krein/Prelude.lean:149` |
| `theorem` | `vacuumChoice_switch_swaps_polarizations_plus` | `lean/InfoGeometry/Krein/Prelude.lean:157` |
| `theorem` | `vacuumChoice_switch_swaps_polarizations_minus` | `lean/InfoGeometry/Krein/Prelude.lean:163` |
| `theorem` | `K_comp_` | `lean/InfoGeometry/Krein/InvolutiveSelfDualCarrier.lean:121` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Krein/Representation.lean:91` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Krein/Representation.lean:98` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Krein/Representation.lean:105` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Krein/Representation.lean:111` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Krein/Representation.lean:117` |
| `def` | `IsKreinSelfAdjoint` | `lean/InfoGeometry/Krein/Modular.lean:38` |
| `def` | `IsKreinSkewAdjoint` | `lean/InfoGeometry/Krein/Modular.lean:42` |
| `def` | `kreinForm` | `lean/InfoGeometry/Krein/Modular.lean:46` |
| `def` | `hilbertPart` | `lean/InfoGeometry/Krein/Modular.lean:50` |
| `def` | `IsKreinPositive` | `lean/InfoGeometry/Krein/Modular.lean:55` |
| `def` | `IsStrictKreinPositive` | `lean/InfoGeometry/Krein/Modular.lean:60` |
| `def` | `IsKreinUnitary` | `lean/InfoGeometry/Krein/Modular.lean:65` |
| `theorem` | `finiteDimensional_krein_polar` | `lean/InfoGeometry/Krein/Modular.lean:79` |
| `def` | `kreinAbs` | `lean/InfoGeometry/Krein/Modular.lean:93` |
| `def` | `ModularFlowBridge` | `lean/InfoGeometry/Krein/Modular.lean:155` |
| `lemma` | `rho_` | `lean/InfoGeometry/Krein/Clifford.lean:110` |
| `lemma` | `rho_` | `lean/InfoGeometry/Krein/Clifford.lean:125` |
| `lemma` | `rho_` | `lean/InfoGeometry/Krein/Clifford.lean:145` |
| `lemma` | `IsKreinIsometry` | `lean/InfoGeometry/Krein/KreinSpace.lean:252` |
| `lemma` | `IsKreinIsometry` | `lean/InfoGeometry/Krein/KreinSpace.lean:254` |
| `lemma` | `IsKreinIsometry` | `lean/InfoGeometry/Krein/KreinSpace.lean:258` |
| `lemma` | `IsKreinIsometry` | `lean/InfoGeometry/Krein/KreinSpace.lean:262` |
| `lemma` | `ThermalVacuum` | `lean/InfoGeometry/Krein/Thermal.lean:180` |
| `lemma` | `ThermalVacuum` | `lean/InfoGeometry/Krein/Thermal.lean:188` |
| `lemma` | `Hom` | `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean:69` |
| `theorem` | `ofMajorana_g_eq_metric` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:25` |
| `theorem` | `ofMajorana_compat` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:35` |
| `theorem` | `ofMajorana_compat_complex_i` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:49` |
| `theorem` | `ofMajorana_` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:63` |
| `theorem` | `modularTransport_commutes_with_projector` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:76` |
| `def` | `QGTRealizesModularVariance` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:84` |
| `theorem` | `qgt_metric_eq_secondMoment_minus_square` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:93` |
| `theorem` | `qgtOfOperator_KRotation_metric_and_berry_invariant` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:106` |
| `theorem` | `kreinQgtOfOperator_KRotation_metric_and_berry_invariant` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:128` |
| `theorem` | `qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_commute_generator` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:148` |
| `theorem` | `qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:176` |
| `theorem` | `kreinQgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis` | `lean/InfoGeometry/Quantum/GeometricTensorTest.lean:205` |
| `theorem` | `dilationChargeResponseMode_of_operatorialIncidence` | `lean/InfoGeometry/Quantum/HestenesKahler.lean:492` |
| `theorem` | `cl11_structural_identities` | `lean/InfoGeometry/Quantum/CliffordDictionaryTest.lean:28` |
| `theorem` | `berry_on_phase_eq_metric_diag` | `lean/InfoGeometry/Quantum/CliffordDictionaryTest.lean:43` |
| `theorem` | `phase_observable_eq_neg_two_mul_inner_fst_snd` | `lean/InfoGeometry/Quantum/CliffordDictionaryTest.lean:65` |
| `lemma` | `Hom` | `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:68` |
| `lemma` | `Hom` | `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:72` |
| `def` | `Hom` | `lean/InfoGeometry/Quantum/RealMajorana.lean:1070` |
| `theorem` | `Hom` | `lean/InfoGeometry/Quantum/RealMajorana.lean:1080` |
| `def` | `Hom` | `lean/InfoGeometry/Quantum/RealMajorana.lean:1091` |
| `theorem` | `Hom` | `lean/InfoGeometry/Quantum/RealMajorana.lean:1105` |
| `theorem` | `Hom` | `lean/InfoGeometry/Quantum/RealMajorana.lean:1126` |
| `lemma` | `ConvexOn` | `lean/InfoGeometry/Geometry/DualFlat.lean:81` |
| `lemma` | `eGeodesicConvex` | `lean/InfoGeometry/Geometry/DualFlat.lean:93` |
| `theorem` | `has` | `lean/InfoGeometry/Geometry/LegendreHessianInverse.lean:16` |
| `lemma` | `IsFenchelConjugate` | `lean/InfoGeometry/Geometry/LegendreDuality.lean:66` |
| `lemma` | `AEAddConst` | `lean/InfoGeometry/Measure/Projective.lean:37` |
| `lemma` | `SameRay` | `lean/InfoGeometry/Measure/Projective.lean:79` |
| `def` | `CartanInvolution` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean:56` |
| `def` | `CartanInvolution` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean:63` |
| `def` | `CartanInvolution` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean:89` |
| `lemma` | `SymmetricPair` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean:115` |
| `theorem` | `natural_gradient_gauge_rotation` | `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:50` |
| `lemma` | `rg_dissipation_bounded_by_anomaly` | `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:68` |
| `theorem` | `omegaSeed_kms_of_jointKernel_commutator_bundle` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:53` |
| `theorem` | `omegaSeed_kms_of_hypotheses` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:67` |
| `def` | `ofModels` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:100` |
| `def` | `ofProofs` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:145` |
| `def` | `expectationSeedReflectionPositivity` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:170` |
| `theorem` | `expectationSeedReflectionPositivity_of_jointKernel_commutator_bundle` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:179` |
| `theorem` | `expectationSeedReflectionPositivity_of_hypotheses` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:189` |
| `def` | `modularReflectionPositivity` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:205` |
| `theorem` | `modularReflectionPositivity_of_positiveTimeVector` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:212` |
| `theorem` | `expectationSeed_and_modularReflectionPositivity_of_jointKernel_commutator_positiveTime` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:223` |
| `theorem` | `expectationSeed_and_modularReflectionPositivity_of_hypotheses` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:240` |
| `def` | `finiteOsterwalderSchraderLayer` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:258` |
| `theorem` | `finiteOsterwalderSchraderLayer_of_positiveTimeVector` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:266` |
| `def` | `finiteWightmanReconstructionLayer` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:279` |
| `theorem` | `finiteWightmanReconstructionLayer_of_expectationSeed` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:291` |
| `def` | `ofExpectationSeedKMS` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:309` |
| `def` | `ofExpectationSeedKMSPositiveTime` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:327` |
| `def` | `ofExpectationSeedKMSFinite` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:347` |
| `def` | `LogDetCoercive` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:370` |
| `lemma` | `gamma_le_spectralGapFromLogDet` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:385` |
| `lemma` | `jacobianRelativeVolume_le_spectralGapFromLogDet` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:392` |
| `theorem` | `spectralGapFromLogDet_pos_of_coercive` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:402` |
| `def` | `ofConcreteLayers` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:434` |
| `def` | `ofExpectationSeedLayers` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:454` |
| `def` | `ofExpectationSeedLayersPositiveTime` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:476` |
| `def` | `ofExpectationSeedLayersFinite` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:499` |
| `def` | `has_su_n_instantiation` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:546` |
| `def` | `has_os_wightman_existence_layer` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:550` |
| `def` | `has_strict_mass_gap` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:558` |
| `lemma` | `asymptotic_freedom_of_bridge_rg_model` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:562` |
| `lemma` | `strict_mass_gap_of_bridge` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:568` |
| `lemma` | `chiral_scale_bounds_mass_gap` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:573` |
| `theorem` | `millennium_obligations_of_bridge` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:578` |
| `theorem` | `millennium_obligations_of_concreteLayers` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:595` |
| `theorem` | `millennium_obligations_of_expectationSeedLayers` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:614` |
| `theorem` | `millennium_obligations_of_expectationSeedLayersPositiveTime` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:637` |
| `theorem` | `millennium_obligations_of_expectationSeedLayersFinite` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:662` |
| `theorem` | `millennium_obligations_of_expectationSeedLayersFiniteFromLogDet` | `lean/InfoGeometry/Unstable/YangMillsBridge.lean:687` |
| `def` | `CompilerTelemetryShadow` | `lean/InfoGeometry/LLM/CompilerRosetta.lean:24` |
| `def` | `CompilerTelemetryShadow` | `lean/InfoGeometry/LLM/CompilerRosetta.lean:30` |
| `def` | `CompilerTelemetryShadow` | `lean/InfoGeometry/LLM/CompilerRosetta.lean:36` |
| `def` | `CompilerTelemetryShadow` | `lean/InfoGeometry/LLM/CompilerRosetta.lean:46` |
| `def` | `ObserverDefectResidualWeylThermodynamicBoundedByZD` | `lean/InfoGeometry/LLM/TrialityMoE.lean:414` |
| `theorem` | `equilibrium_of_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:78` |
| `theorem` | `sourcedGenerator_deviation_eq_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:84` |
| `theorem` | `noncommutingScaleLane_of_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:286` |
| `theorem` | `not_detailedEquilibrium_of_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:302` |
| `theorem` | `trajectoryRNBarrierNext_add_availableWorkRN_eq_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:492` |
| `theorem` | `trajectoryRNBarrierNext_add_dissipatedHeatRN_eq_` | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:503` |
| `def` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Bundle.lean:13` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Bundle.lean:16` |
| `def` | `GaugeEquivalent` | `lean/InfoGeometry/Prequantum/Quotient.lean:31` |
| `lemma` | `gaugeEquivalent_refl` | `lean/InfoGeometry/Prequantum/Quotient.lean:35` |
| `lemma` | `gaugeEquivalent_symm` | `lean/InfoGeometry/Prequantum/Quotient.lean:40` |
| `lemma` | `gaugeEquivalent_trans` | `lean/InfoGeometry/Prequantum/Quotient.lean:48` |
| `def` | `gaugeSetoid` | `lean/InfoGeometry/Prequantum/Quotient.lean:59` |
| `lemma` | `covariantDerivative_constant_on_orbits` | `lean/InfoGeometry/Prequantum/Quotient.lean:65` |
| `theorem` | `eq_iff` | `lean/InfoGeometry/Prequantum/Quotient.lean:102` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Scaling.lean:34` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Scaling.lean:40` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Scaling.lean:57` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Scaling.lean:61` |
| `theorem` | `PrequantumData` | `lean/InfoGeometry/Prequantum/Scaling.lean:65` |
| `def` | `connectionScale` | `lean/InfoGeometry/Prequantum/Scaling.lean:104` |
| `def` | `covariantScale` | `lean/InfoGeometry/Prequantum/Scaling.lean:113` |
| `def` | `GaugeEquivalent` | `lean/InfoGeometry/Prequantum/Scaling.lean:129` |
| `lemma` | `gaugeEquivalent_refl` | `lean/InfoGeometry/Prequantum/Scaling.lean:132` |
| `lemma` | `gaugeEquivalent_symm` | `lean/InfoGeometry/Prequantum/Scaling.lean:137` |
| `lemma` | `gaugeEquivalent_trans` | `lean/InfoGeometry/Prequantum/Scaling.lean:144` |
| `def` | `gaugeSetoid` | `lean/InfoGeometry/Prequantum/Scaling.lean:154` |
| `def` | `connectionObservable` | `lean/InfoGeometry/Prequantum/Connection.lean:46` |
| `def` | `covariantDerivative` | `lean/InfoGeometry/Prequantum/Connection.lean:50` |
| `lemma` | `connectionObservable_gauge` | `lean/InfoGeometry/Prequantum/Connection.lean:53` |
| `lemma` | `hessian_indefinite_form_smul_smul_weyl` | `lean/InfoGeometry/Prequantum/Connection.lean:69` |
| `def` | `constantValue` | `lean/InfoGeometry/Meta/DrazinRefactor.lean:53` |
| `def` | `DeclRole` | `lean/InfoGeometry/Meta/StrictSurface.lean:20` |
| `def` | `AdmissionDecision` | `lean/InfoGeometry/Meta/Admission.lean:63` |
| `def` | `RepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:19` |
| `def` | `RepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:28` |
| `def` | `RepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:43` |
| `def` | `RepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:52` |
| `def` | `RepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:61` |
| `def` | `parseRepDepth` | `lean/InfoGeometry/Meta/Architecture.lean:68` |
| `def` | `repDepth` | `lean/InfoGeometry/Meta/Architecture.lean:101` |
| `def` | `ProofHeadShape` | `lean/InfoGeometry/Meta/ProofShape.lean:40` |
| `def` | `StatementShape` | `lean/InfoGeometry/Meta/ProofShape.lean:48` |
| `def` | `ThinSurfaceKind` | `lean/InfoGeometry/Meta/ProofShape.lean:56` |
| `def` | `ProofHeadShape` | `lean/InfoGeometry/Meta/ProofShape.lean:109` |
| `def` | `ProofHeadShape` | `lean/InfoGeometry/Meta/ProofShape.lean:116` |
| `theorem` | `InformationKillingField` | `lean/InfoGeometry/Canonical/NoetherInference.lean:53` |
| `def` | `BayesianSymmetryOrbit` | `lean/InfoGeometry/Canonical/NoetherInference.lean:372` |
| `theorem` | `IsGaugeBalanced` | `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean:177` |
| `theorem` | `TwistorHodgePalatialBridgeContext` | `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:95` |
| `theorem` | `TwistorHodgePalatialBridgeContext` | `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:112` |
| `theorem` | `TwistorHodgePalatialBridgeContext` | `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:134` |
| `theorem` | `superTemperature_zero_odd` | `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean:62` |
| `theorem` | `diracMassTerm_is_equilibrium_constant` | `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean:74` |
| `def` | `chiralEquilibrium` | `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean:84` |
| `def` | `OperatorialMetricResponsePSD` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:230` |
| `theorem` | `canonicalEntropyProduction_nonneg_of_cramerRaoResponse` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:563` |
| `theorem` | `canonicalEntropyProduction_nonneg_of_regularCone` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:581` |
| `theorem` | `supergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:600` |
| `theorem` | `operatorialEntropyProduction_xChannel_nonneg_of_regularCone` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:633` |
| `theorem` | `weylCovariantThermodynamicDerivation_eq_zeroWeight_add_phaseAxis` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:724` |
| `theorem` | `operatorialDilationGoldstoneCharge_packet` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:744` |
| `theorem` | `supergradedFisherOnsagerBlock_squareResponse_CAR_packet` | `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean:786` |
| `theorem` | `positiveRay_logGenerator_eq_relativeModularPotential_ae` | `lean/InfoGeometry/Canonical/PositiveRayProjectiveBridge.lean:44` |
| `theorem` | `positiveRay_logGenerator_eq_relativeModularPotential` | `lean/InfoGeometry/Canonical/PositiveRayProjectiveBridge.lean:54` |
| `def` | `UnificationComplete` | `lean/InfoGeometry/Canonical/GrandUnificationBlueprint.lean:71` |
| `lemma` | `SinkhornKMSCapstone` | `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:39` |
| `lemma` | `FullThermoGeoIndexCapstone` | `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:104` |
| `lemma` | `FullThermoGeoIndexCapstone` | `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:116` |
| `def` | `IsCompactBeliefUpdate` | `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:51` |
| `def` | `IsNonCompactBeliefUpdate` | `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:59` |
| `theorem` | `anomaly_as_structure_constant` | `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:68` |
| `theorem` | `cartan_collapse_of_normal` | `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:80` |
| `theorem` | `cartan_collapse_of_unitRelativeVolume` | `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:97` |
| `theorem` | `canopy_unitRelativeVolumeState` | `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:37` |
| `theorem` | `canopy_isRicciFlat_and_vacuumEinstein` | `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:52` |
| `theorem` | `calabiYau_trunk_to_canopy_closure` | `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:70` |
| `theorem` | `calabiYau_root_factorization` | `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:89` |
| `theorem` | `drazinTranslationCandidate_isSpectralCompact` | `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:192` |
| `theorem` | `unified_sources_sinks_onsager_with_internal_central_split` | `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:756` |
| `theorem` | `unified_internal_split_with_operatorial_shadow` | `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:835` |
| `theorem` | `isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume` | `lean/InfoGeometry/Canonical/IncompressibleBitBridge.lean:207` |
| `def` | `AdmissibleTemperatureCone` | `lean/InfoGeometry/Canonical/SouriauPlanckVector.lean:56` |
| `theorem` | `fisherBilinAt_eq_channelKreinMetricAtState` | `lean/InfoGeometry/Canonical/NoetherRelationalBridge.lean:42` |
| `def` | `ChiralChargeFockNumberReconciliation` | `lean/InfoGeometry/Canonical/ChiralChargeFockNumberBridge.lean:188` |
| `def` | `ChiralLightconeKKTClosure` | `lean/InfoGeometry/Canonical/ChiralChargeFockNumberBridge.lean:204` |
| `theorem` | `IBMarginalDescentWitness` | `lean/InfoGeometry/Canonical/IBPythagorean.lean:491` |
| `theorem` | `conformal_ward_identity` | `lean/InfoGeometry/Canonical/ConformalWard.lean:31` |
| `def` | `projectorMismatchAnomaly` | `lean/InfoGeometry/Canonical/ProjectorAnomalyConformalBridge.lean:38` |
| `theorem` | `anomaly_vanishes_of_commute` | `lean/InfoGeometry/Canonical/ProjectorAnomalyConformalBridge.lean:45` |
| `theorem` | `projector_anomaly_is_conformal_generator` | `lean/InfoGeometry/Canonical/ProjectorAnomalyConformalBridge.lean:68` |
| `def` | `IsClockFaithfulExponentialBranch` | `lean/InfoGeometry/Canonical/WindingOrbitClosure.lean:238` |
| `theorem` | `topologicalBekensteinBound_of_connesCocycle_generatorLift_zero` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:418` |
| `theorem` | `topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:647` |
| `theorem` | `audit_finite_inverseFisherMetric_of_det_ne_zero` | `lean/InfoGeometry/Canonical/SouriauTranslatorAudit.lean:181` |
| `theorem` | `constructive_logDetRN_packet` | `lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean:119` |
| `theorem` | `stateFirst_modularSplit_singularClosure_operatorialCramerRao` | `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk1.lean:71` |
| `theorem` | `exists_nontrivial_regularization_pair_of_dim_mismatch` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:134` |
| `theorem` | `KKTClosureSymmetry` | `lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean:193` |
| `theorem` | `operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization` | `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:342` |
| `theorem` | `neg_log_abs_jac_det_clm_comp` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:38` |
| `def` | `satisfies_spinorial_dissipation_law` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:55` |
| `def` | `satisfies_normalized_constant_spinorial_tracking_law` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:64` |
| `theorem` | `w_monotone_of_normalized_constant_spinorial_tracking_law` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:71` |
| `theorem` | `w_monotone_of_spinorial_dissipation_lower_bound` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:87` |
| `theorem` | `w_strict_mono_of_normalized_constant_spinorial_tracking_law` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:100` |
| `theorem` | `gravity_from_rn_entropy` | `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:122` |
| `def` | `EmergentTimeFlow` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean:36` |
| `theorem` | `emergentTimeFlow_of_sinkhornTrajectory` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean:40` |
| `theorem` | `anomalyScalePhase_of_nonzeroAnomaly` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean:54` |
| `theorem` | `pathDependence_of_twistedInference` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean:68` |
| `theorem` | `exists_gaugeOrderHysteresis_witness` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean:74` |
| `def` | `finiteInverseZeta` | `lean/InfoGeometry/Canonical/AnalyticLimit.lean:29` |
| `theorem` | `finiteInverseZeta_eq_finiteEulerProduct` | `lean/InfoGeometry/Canonical/AnalyticLimit.lean:36` |
| `theorem` | `inverseZeta_eq_tendsto_finiteInverseZeta` | `lean/InfoGeometry/Canonical/AnalyticLimit.lean:61` |
| `def` | `ofMomentImage` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:99` |
| `def` | `ofMomentImageSquareDissipation` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:142` |
| `theorem` | `casimir_leaf_transverse_onsager_square_packet` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:281` |
| `theorem` | `coadjoint_orbit_metriplectic_second_law` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:377` |
| `theorem` | `full_infinite_dimensional_coadjoint_orbit_hessian_theorem` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:1296` |
| `theorem` | `full_smooth_legendre_square_dissipation_constructive_theorem` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:1714` |
| `theorem` | `full_smooth_legendre_gram_square_dissipation_constructive_theorem` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:1775` |
| `theorem` | `full_smooth_legendre_gram_square_dissipation_inverse_laws_theorem` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:1852` |
| `theorem` | `full_cle_legendre_gram_square_dissipation_constructive_theorem` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:1936` |
| `theorem` | `fisher_onsager_metriplectic_constructive_proof_packet` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:2013` |
| `theorem` | `gibbs_souriau_integral_covariance_to_metriplectic_packet` | `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean:2098` |
| `lemma` | `SameScoreRay` | `lean/InfoGeometry/Canonical/IBProjective.lean:77` |
| `lemma` | `SameScoreRay` | `lean/InfoGeometry/Canonical/IBProjective.lean:90` |
| `theorem` | `semanticCollapsePacket_of_equilibriumSeed_of_structuredProjectorHypotheses` | `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean:199` |
| `theorem` | `PlusRestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean:62` |
| `theorem` | `MinusRestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean:67` |
| `theorem` | `souriauFisherOnsager_proof_packet` | `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean:519` |
| `theorem` | `gibbsSouriau_massieu_fisher_onsager_secondLaw_packet` | `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean:581` |
| `theorem` | `canonical_split_with_intrinsic_nonScalar_and_index_shadow` | `lean/InfoGeometry/Canonical/DrazinSupercharge.lean:1518` |
| `theorem` | `partitionFunction_is_souriau_character` | `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean:50` |
| `theorem` | `denominator_is_prime_euler_product` | `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean:57` |
| `theorem` | `parity_trace_witness` | `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean:63` |
| `def` | `concreteInterfacePackage` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:42` |
| `theorem` | `concreteInterfacePackage_isCStarReady` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:53` |
| `theorem` | `concreteInterfacePackage_isCompleteCStarReady` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:63` |
| `theorem` | `sinkhornEndpointClosure` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:73` |
| `theorem` | `aqft_trunk_to_canopy_closure` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:108` |
| `theorem` | `aqft_root_factorization` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:123` |
| `theorem` | `aqft_isomorphism_corridor` | `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:137` |
| `theorem` | `RelativeModularBridge` | `lean/InfoGeometry/Canonical/StandardFormCore.lean:246` |
| `theorem` | `target` | `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean:407` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:38` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:68` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:93` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:117` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:144` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:167` |
| `theorem` | `RestrictedRelativeModularData` | `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:202` |
| `theorem` | `local_cancellation_packet` | `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean:129` |
| `theorem` | `operatorPartition_eq_operatorSupercharacter` | `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean:459` |
| `theorem` | `transformWeylGauge_preserves_closure` | `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean:1013` |
| `def` | `finiteFockChemicalPotentialAffineFunctor` | `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean:1228` |
| `def` | `SatisfiesWeylGrandCanonicalTKKKKTBridge` | `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean:1282` |
| `theorem` | `RelativeStatePair` | `lean/InfoGeometry/Canonical/RelativeModularOperator.lean:78` |
| `theorem` | `relativeInformationEnergy_finiteShadow_eq_sum_gauge_sq_neg_log_relativeModularOperator_diag` | `lean/InfoGeometry/Canonical/RelativeModularOperator.lean:410` |
| `theorem` | `relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit` | `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:201` |
| `theorem` | `relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit` | `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:280` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean:135` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean:141` |
| `def` | `ChiralSliceModularCliffordTransportAlong` | `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:703` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:59` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:65` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:71` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:77` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:88` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:95` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:149` |
| `def` | `PolarizedRecompositionData` | `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:156` |
| `theorem` | `operatorMassieu_eq_log_generalizedBerezinianScale_of_operatorPartition_eq_generalizedBerezinianScale` | `lean/InfoGeometry/Canonical/OperatorPartitionSupervolumeBridge.lean:48` |
| `theorem` | `cpt_gap_hessian_centralCharge_closure` | `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean:162` |
| `theorem` | `cpt_gap_hessian_parity_kkt_closure` | `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean:196` |
| `theorem` | `root_supercharge_lichnerowicz_centralCharge_closure` | `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean:342` |
| `theorem` | `root_central_supercharge_theorem` | `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean:432` |
| `theorem` | `unified_supercharge_central_supergeometry_topological_closure` | `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean:480` |
| `theorem` | `oddOddBracket_eq_translation_plus_central_plus_defectResidual` | `lean/InfoGeometry/Canonical/UnifiedSuperchargeOddOddBridge.lean:119` |
| `def` | `SignedContribution` | `lean/InfoGeometry/Canonical/SignedParticleBridge.lean:42` |
| `def` | `parallelTransportE` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean:38` |
| `lemma` | `radonNikodymOp_pos` | `lean/InfoGeometry/Canonical/BeliefDynamics.lean:72` |
| `theorem` | `hestenesWeylModularBerryPhaseReadout_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart` | `lean/InfoGeometry/Canonical/BerryPhase.lean:43` |
| `theorem` | `informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex` | `lean/InfoGeometry/Canonical/BerryPhase.lean:65` |
| `theorem` | `informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank` | `lean/InfoGeometry/Canonical/BerryPhase.lean:71` |
| `theorem` | `informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero` | `lean/InfoGeometry/Canonical/BerryPhase.lean:81` |
| `theorem` | `berry_phase_vanishes_for_normal` | `lean/InfoGeometry/Canonical/BerryPhase.lean:90` |
| `def` | `innerDerivation` | `lean/InfoGeometry/Canonical/OperatorialFierzDerivationBridge.lean:52` |
| `def` | `emergentSpacetimeDerivation` | `lean/InfoGeometry/Canonical/OperatorialFierzDerivationBridge.lean:79` |
| `def` | `SpacetimeIsThermalFlow` | `lean/InfoGeometry/Canonical/OperatorialFierzDerivationBridge.lean:89` |
| `theorem` | `emergentSpacetime_is_derivation` | `lean/InfoGeometry/Canonical/OperatorialFierzDerivationBridge.lean:98` |
| `theorem` | `centralOperator_isDrazinLaneCentral` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:148` |
| `theorem` | `centralOperator_isDefectSupported` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:156` |
| `theorem` | `supercharge_in_chiralCone` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:164` |
| `theorem` | `superHamiltonian_eq_K0_plus_centralOperator` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:172` |
| `theorem` | `centralOperator_isDrazinLaneCentral` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:218` |
| `theorem` | `centralOperator_isDefectSupported` | `lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean:226` |
| `theorem` | `deriv2_scalarLogReadout_zero_eq_probe_modularLieHessian_of_stationary` | `lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean:258` |
| `theorem` | `dilation_anomaly_jacobi_expansion` | `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:39` |
| `theorem` | `trace_dilation_eq_zero` | `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:59` |
| `theorem` | `normal_phase_of_trace_anomaly_in_finite_dim` | `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:77` |
| `def` | `firstQuantizationChemicalPotentialAffineBridge` | `lean/InfoGeometry/Canonical/GrandCanonicalFockNumberBridge.lean:153` |
| `theorem` | `unitOfAction_eq_metricVolumePotential` | `lean/InfoGeometry/Canonical/IncompressibleCramerRaoActionBridge.lean:168` |
| `theorem` | `SinkhornRicciIndexInvariant` | `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:51` |
| `theorem` | `SinkhornRicciIndexInvariant` | `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:68` |
| `theorem` | `SinkhornRicciIndexInvariant` | `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:96` |
| `theorem` | `SinkhornRicciIndexInvariant` | `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:134` |
| `theorem` | `SpectroscopicKMSCompatible` | `lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean:61` |
| `theorem` | `drazin_dilation_anomaly_corridor` | `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:41` |
| `theorem` | `chiral_anomaly_is_skew_adjoint` | `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:54` |
| `theorem` | `anomaly_owner_packet` | `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:66` |
| `theorem` | `projector_noncommutativity_closure_packet` | `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:98` |
| `theorem` | `parity_trace_witness_is_owner` | `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:115` |
| `theorem` | `log_defined_on_` | `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean:167` |
| `theorem` | `log_defined_on_` | `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean:185` |
| `theorem` | `claimD_scalarLegendre_inverseHessian_eq_inv_fisher` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:107` |
| `theorem` | `claimD_fenchelLegendre_contact_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:258` |
| `theorem` | `structuredSouriauTranslatorPacket` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:327` |
| `theorem` | `claimK_kktEntropyStationarity_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:411` |
| `theorem` | `claimW_representationWeight_lifts_to_densityTransport` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:433` |
| `theorem` | `claimS_superCoadjoint_stress_supercurrent_readouts` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:451` |
| `theorem` | `claimF_superSouriauFermionGas_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:477` |
| `theorem` | `claimF_superSouriauFermionGas_packet_ofIdentityBalancedStress` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:543` |
| `theorem` | `claimG_infiniteSuperCoadjointMetriplectic_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:633` |
| `theorem` | `claimT_splitCl44_TKK_JordanLie_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:673` |
| `theorem` | `claimM_coadjointLeaf_Casimir_transverseOnsager_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:718` |
| `theorem` | `structuredSouriauKKTTranslatorPacket` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:746` |
| `theorem` | `analyticEnrichmentTranslatorPacket` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:866` |
| `theorem` | `claimCD_fullCoadjointOrbit_hessian_packet` | `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean:889` |
| `theorem` | `onsager_total_entropy_nonnegative` | `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean:171` |
| `def` | `toCoordinatelessSouriauFisherContext` | `lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean:960` |
| `def` | `WeylSupertraceFreeStressContext` | `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean:391` |
| `theorem` | `entropyFoliation_transverseOnsager_weylCovariant_packet` | `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean:666` |
| `theorem` | `squareEntropyFoliation_transverseOnsager_weylCovariant_packet` | `lean/InfoGeometry/Canonical/LiteratureGrandCanonicalWeylTKK.lean:718` |
| `theorem` | `certified_operator_ratio_regularization_corridor` | `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean:151` |
| `theorem` | `certified_operator_ratio_regularization_kills_defect_of_alignment` | `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean:189` |
| `def` | `Bridge` | `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:24` |
| `def` | `Bridge` | `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:27` |
| `theorem` | `splitCl44_TKK_JordanLie_constructive_packet` | `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean:189` |
| `theorem` | `fisherKilling_baseRelation_transports` | `lean/InfoGeometry/Canonical/SplitCl44TKKJordanLieBridge.lean:252` |
| `theorem` | `log_defined_on_` | `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean:46` |
| `theorem` | `log_defined_on_` | `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean:58` |
| `def` | `spineFunctorKind` | `lean/InfoGeometry/Canonical/SpineAttributes.lean:122` |
| `theorem` | `densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed` | `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:283` |
| `def` | `PrimeGasJaynesConjecture` | `lean/InfoGeometry/Canonical/OpenProblemFormalization.lean:404` |
| `lemma` | `boltzmannRelativeVolumeEntropy_eq_divergence` | `lean/InfoGeometry/Canonical/ChiralTorsionRelativeVolume.lean:25` |
| `theorem` | `canonicalDIIIProxy_transport_root_index_commutator_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:393` |
| `theorem` | `canonicalDIIIProxy_transport_root_centralCharge_commutator_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:449` |
| `theorem` | `canonicalDIIIProxy_transport_parity_kkt_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:505` |
| `theorem` | `canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:654` |
| `theorem` | `canonicalDIIIProxy_transport_root_parity_vorticity_kkt_headSuperBracket_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:732` |
| `theorem` | `canonicalDIIIProxy_transport_root_parity_vortexWitness_kkt_headSuperBracket_closure` | `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean:810` |
| `def` | `ConstructiveClosureDrazinData` | `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean:204` |
| `theorem` | `log_defined_on_` | `lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean:54` |
| `theorem` | `DilationWitness` | `lean/InfoGeometry/Canonical/DilationKKTBridge.lean:32` |
| `theorem` | `bayesian_inference_as_creation` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:23` |
| `theorem` | `data_model_split_is_projector_split` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:30` |
| `theorem` | `majorana_belief_iff_zero_uncertainty` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:42` |
| `theorem` | `fierz_power_conservation` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:48` |
| `theorem` | `super_even_even_eq_commutator` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:62` |
| `theorem` | `super_odd_odd_eq_anticommutator` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:70` |
| `theorem` | `einstein_inducedChemicalPotential_eq_transportedResidual` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:88` |
| `theorem` | `grandCanonical_eq_hamiltonian_of_vacuumTransported` | `lean/InfoGeometry/Canonical/SUSYBayes.lean:96` |
| `theorem` | `baNormalize_pointwise_massNndist_le_of_massRecipLipschitz` | `lean/InfoGeometry/Canonical/IBUpdate.lean:1069` |
| `theorem` | `exists_internal_split_with_intrinsic_nonScalar_shadow` | `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean:162` |
| `theorem` | `intrinsic_nonScalar_shadow_witness` | `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean:257` |
| `theorem` | `names` | `lean/InfoGeometry/Canonical/All.lean:536` |
| `theorem` | `coordinateFreeWeylLieDerivation_packet` | `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean:105` |
| `theorem` | `densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed` | `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean:188` |
| `theorem` | `densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis` | `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean:228` |
| `def` | `identityBalanced` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:225` |
| `def` | `ofMomentImageSquareDissipation` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:335` |
| `def` | `ofIdentityBalancedSquareDissipation` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:401` |
| `theorem` | `dimensionAgnostic_squareDissipation_secondLaw` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:608` |
| `theorem` | `finite_inverseFisherMetric_of_det_ne_zero` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:808` |
| `theorem` | `finite_Hessian_eq_Fisher_eq_Onsager` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:840` |
| `theorem` | `finite_FisherOnsager_entropyProduction_nonneg_of_det_nonneg` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:879` |
| `theorem` | `operatorialSouriauFisherMetric_packet_of_cramerRaoResponse` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:1222` |
| `theorem` | `operatorialXChannel_entropyProduction_nonneg_of_regularCone` | `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:1305` |
| `lemma` | `FrozenFiniteRegime` | `lean/InfoGeometry/Canonical/IBBase.lean:228` |
| `lemma` | `FrozenFiniteRegime` | `lean/InfoGeometry/Canonical/IBBase.lean:238` |
| `lemma` | `FrozenFiniteRegime` | `lean/InfoGeometry/Canonical/IBBase.lean:250` |
| `lemma` | `FrozenFiniteRegime` | `lean/InfoGeometry/Canonical/IBBase.lean:262` |
| `def` | `RelativeStatePair` | `lean/InfoGeometry/Canonical/RelativeModularCore.lean:67` |
| `def` | `FlatCurvatureValueBridge` | `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:40` |
| `def` | `FlatCurvatureProjectorObstructionBridge` | `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:59` |
| `def` | `FlatCurvatureChiralScaleBridge` | `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:69` |
| `theorem` | `operatorInformationHessian_eq_double_transportCommutator` | `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean:301` |
| `theorem` | `GeneralizedMetricSeed` | `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean:63` |
| `theorem` | `chiral_action_reduces_for_normal` | `lean/InfoGeometry/Canonical/ChiralAction.lean:37` |
| `theorem` | `chiralDirac_eq_of_unitRelativeVolume` | `lean/InfoGeometry/Canonical/ChiralAction.lean:59` |
| `theorem` | `RealSplitCl11Action` | `lean/InfoGeometry/Canonical/KKTCore.lean:108` |
| `def` | `SpectralChiralConeAlgebra` | `lean/InfoGeometry/Canonical/ChiralOperatorConeClosure.lean:426` |
| `theorem` | `relativeModularSupervolume_secondVariation_is_sinkhornPerelmanKreinMetric` | `lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean:403` |
| `def` | `multinomialStatistic` | `lean/InfoGeometry/ExponentialFamily/Class.lean:50` |
| `def` | `multinomialLogPartition` | `lean/InfoGeometry/ExponentialFamily/Class.lean:54` |
| `def` | `multinomialDensity` | `lean/InfoGeometry/ExponentialFamily/Class.lean:58` |
| `lemma` | `multinomial_partition_pos` | `lean/InfoGeometry/ExponentialFamily/Class.lean:63` |
| `lemma` | `multinomial_density_pos` | `lean/InfoGeometry/ExponentialFamily/Class.lean:76` |
| `lemma` | `multinomial_density_eq` | `lean/InfoGeometry/ExponentialFamily/Class.lean:85` |
| `lemma` | `multinomial_normalization` | `lean/InfoGeometry/ExponentialFamily/Class.lean:97` |
| `theorem` | `thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` | `lean/InfoGeometry/Convex/Legendre.lean:260` |
| `lemma` | `SPD` | `lean/InfoGeometry/Jordan/SPD.lean:21` |
| `lemma` | `SPD` | `lean/InfoGeometry/Jordan/SPD.lean:25` |
| `lemma` | `SPD` | `lean/InfoGeometry/Jordan/LogDet.lean:25` |
| `lemma` | `SPD` | `lean/InfoGeometry/Jordan/LogDet.lean:29` |
| `lemma` | `SatisfiesIntegrable` | `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean:44` |
| `lemma` | `SatisfiesIntegrable` | `lean/InfoGeometry/MaxEnt/Core.lean:76` |
| `lemma` | `IsMaxEntSolution` | `lean/InfoGeometry/MaxEnt/Core.lean:139` |
| `theorem` | `IsMaxEntSolution` | `lean/InfoGeometry/MaxEnt/Core.lean:194` |
| `lemma` | `BurgModel` | `lean/InfoGeometry/MaxEnt/Jaynes.lean:575` |
| `theorem` | `ray_smul` | `lean/InfoGeometry/Projective/GaugeQuotient.lean:39` |
| `theorem` | `projectiveClassToTwistor_val` | `lean/InfoGeometry/Projective/TwistorBridge.lean:94` |
| `lemma` | `projectiveClassToTwistor_mk_normalize` | `lean/InfoGeometry/Projective/TwistorBridge.lean:105` |
| `lemma` | `projectiveClassToTwistor_normalizeOnProj` | `lean/InfoGeometry/Projective/TwistorBridge.lean:123` |
| `lemma` | `SameRay` | `lean/InfoGeometry/Projective/Projective.lean:29` |
| `lemma` | `SameRay` | `lean/InfoGeometry/Projective/Projective.lean:35` |
| `lemma` | `modular_j_complex_i_anticommute` | `lean/InfoGeometry/Clifford/Lift.lean:21` |
| `lemma` | `cl11RepLin_apply_pair` | `lean/InfoGeometry/Clifford/Lift.lean:33` |
| `lemma` | `cl11RepLin_sq` | `lean/InfoGeometry/Clifford/Lift.lean:40` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Clifford/Lift.lean:54` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Clifford/Lift.lean:58` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Clifford/Lift.lean:63` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Clifford/Lift.lean:70` |
| `lemma` | `cl11Rep_` | `lean/InfoGeometry/Clifford/Lift.lean:77` |
| `lemma` | `cl11Rep_pseudoscalar` | `lean/InfoGeometry/Clifford/Lift.lean:86` |
| `lemma` | `oddTriple_skew` | `lean/InfoGeometry/Core/SymmetricLie.lean:666` |
| `lemma` | `mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:41` |
| `lemma` | `mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:51` |
| `lemma` | `P_plus_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:95` |
| `lemma` | `P_minus_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:99` |
| `lemma` | `P_plus_eq_self_of_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:103` |
| `lemma` | `P_minus_eq_zero_of_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:112` |
| `lemma` | `P_plus_eq_zero_of_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:120` |
| `lemma` | `P_minus_eq_self_of_mem_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:128` |
| `theorem` | `disjoint_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:199` |
| `theorem` | `sup_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:209` |
| `theorem` | `isCompl_` | `lean/InfoGeometry/Core/SymmetricLieGeneric.lean:217` |
| `def` | `SymmetricSpace` | `lean/InfoGeometry/Core/UnifiedGeometry.lean:49` |
| `def` | `SymmetricSpace` | `lean/InfoGeometry/Core/UnifiedGeometry.lean:58` |
| `def` | `Symphony` | `lean/InfoGeometry/Exploration/Symphony/Draft.lean:38` |
| `def` | `symphonyPreservationClaim` | `lean/InfoGeometry/Exploration/Symphony/Draft.lean:58` |
| `def` | `SymphonyDensity` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:18` |
| `def` | `IsBalanced` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:27` |
| `theorem` | `symphony_cancellation` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:37` |
| `def` | `active_projector` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:65` |
| `theorem` | `active_projector_of_compat` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:72` |
| `theorem` | `active_projector_unique_of_indices` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:83` |
| `theorem` | `active_projector_preserves_balance` | `lean/InfoGeometry/Exploration/Symphony/Basic.lean:97` |

## 🏝️ Theory Islands (Disjoint Components)

### Island 1 (25628 decls)
  - `InfoGeometry.Algebraic.Fitting.AscentStabilized`
  - `InfoGeometry.Algebraic.Fitting.DescentStabilized`
  - `InfoGeometry.Algebraic.Fitting.ascent_le`
  - `InfoGeometry.Algebraic.Fitting.descent_le`
  - `InfoGeometry.Algebraic.Fitting.injective_on_range`
  - `InfoGeometry.Algebraic.Fitting.isCompl_ker_pow_range_pow`
  - `InfoGeometry.Algebraic.Fitting.ker_pow_eq_of_ascent_stabilized`
  - `InfoGeometry.Algebraic.Fitting.range_pow_eq_of_descent_stabilized`
  - `InfoGeometry.Algebraic.Fitting.surjective_on_range`
  - `InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance`
  - `InfoGeometry.Analytic.deriv_firstMomentUnnormalized`
  - `InfoGeometry.Analytic.deriv_logSumExpMoment1`
  - `InfoGeometry.Analytic.deriv_logSumExpPartition`
  - `InfoGeometry.Analytic.deriv_logSumExp_eq_firstMoment_div_partition`
  - `InfoGeometry.Analytic.deriv_logSumExp_eq_softmaxMean`
  - `InfoGeometry.Analytic.deriv_softmaxPartition`
  - `InfoGeometry.Analytic.firstMomentUnnormalized`
  - `InfoGeometry.Analytic.hasDerivAt_firstMomentUnnormalized`
  - `InfoGeometry.Analytic.hasDerivAt_logSumExpMoment1`
  - `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition`
  - ... and 25608 more
### Island 2 (427 decls)
  - `InfoGeometry.Meta.AdmissionDecision`
  - `InfoGeometry.Meta.AdmissionDecision.admitted`
  - `InfoGeometry.Meta.AdmissionDecision.admitted.elim`
  - `InfoGeometry.Meta.AdmissionDecision.admitted.sizeOf_spec`
  - `InfoGeometry.Meta.AdmissionDecision.asString`
  - `InfoGeometry.Meta.AdmissionDecision.blocked`
  - `InfoGeometry.Meta.AdmissionDecision.blocked.elim`
  - `InfoGeometry.Meta.AdmissionDecision.blocked.sizeOf_spec`
  - `InfoGeometry.Meta.AdmissionDecision.casesOn`
  - `InfoGeometry.Meta.AdmissionDecision.ctorElim`
  - `InfoGeometry.Meta.AdmissionDecision.ctorElimType`
  - `InfoGeometry.Meta.AdmissionDecision.ctorIdx`
  - `InfoGeometry.Meta.AdmissionDecision.needsReview`
  - `InfoGeometry.Meta.AdmissionDecision.needsReview.elim`
  - `InfoGeometry.Meta.AdmissionDecision.needsReview.sizeOf_spec`
  - `InfoGeometry.Meta.AdmissionDecision.noConfusion`
  - `InfoGeometry.Meta.AdmissionDecision.noConfusionType`
  - `InfoGeometry.Meta.AdmissionDecision.notPromotable`
  - `InfoGeometry.Meta.AdmissionDecision.notPromotable.elim`
  - `InfoGeometry.Meta.AdmissionDecision.notPromotable.sizeOf_spec`
  - ... and 407 more
### Island 3 (323 decls)
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.bilinearOperatorProduct`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.casesOn`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.fierz_decomposition`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.gravityPotential_eq_spinTwo`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.gravityPotential_eq_spinTwoChannel`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.linearizedGravityPotential`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.mk`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.mk.inj`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.mk.noConfusion`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.mk.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.noConfusion`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.rec`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.recOn`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.scalarChannel`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.spinTwoChannel`
  - `InfoGeometry.SuperMetriplectic.FierzSpinTwoExtractionPacket.vectorChannel`
  - `InfoGeometry.SuperMetriplectic.OperatorBKMHessianPacket`
  - ... and 303 more
### Island 4 (194 decls)
  - `InfoGeometry.Canonical.Spin44CharacterShadow.Cartan4`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.EvenMinus`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.OddMinus`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.decidableEvenMinus`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.decidableOddMinus`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.diracSpinorCharacter`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.evenMinus_card`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.halfSignedPairing`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.halfSpinorDifferenceShadow`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.halfSpinorDifferenceShadow_eq`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.minusCount`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.oddMinus_card`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.signOfBool`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.spinorEvenCharacter`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.spinorOddCharacter`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.vectorCharacter`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.vectorCharacterCosh`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.vectorCharacter_eq_two_sum_cosh`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.vectorMinusDiracSupertraceShadow`
  - `InfoGeometry.Canonical.Spin44CharacterShadow.vectorMinusDiracSupertraceShadow_eq`
  - ... and 174 more
### Island 5 (188 decls)
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.bracketClosed`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.cartanCarrier`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.casesOn`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.ctorIdx`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.includeInLieAlgebra`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.mk`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.mk.inj`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.noConfusion`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.noConfusionType`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.rec`
  - `InfoGeometry.Canonical.SouriauThermodynamics.CartanSubalgebra.recOn`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature.carrier`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature.casesOn`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature.ctorIdx`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature.mk`
  - `InfoGeometry.Canonical.SouriauThermodynamics.SouriauCartanTemperature.mk.inj`
  - ... and 168 more
### Island 6 (166 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.Density`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.KLAsBregmanDivergence`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.affineCocycleWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.betaAction`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.coadjointAction`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.cocycle`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.groupAction`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.partitionPotentialAffineCorrection`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.rec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.recOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.LieCovarianceAndCocycle.souriau`
  - ... and 146 more
### Island 7 (162 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.concrete_majorana_bdg_four_by_four`
  - `InfoGeometry.Canonical.OpenProblemFormalization.concrete_real_four_by_four_biquaternion_slice`
  - `InfoGeometry.Canonical.OpenProblemFormalization.concrete_real_pfaffian_bridge`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a12`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a13`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a14`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a23`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a24`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.a34`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.casesOn`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.ctorIdx`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.mk`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.mk.inj`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.mk.noConfusion`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.mk.sizeOf_spec`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.noConfusion`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.noConfusionType`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.rec`
  - `InfoGeometry.Clifford.HestenesDirac.MajoranaBdGCoordinates.recOn`
  - ... and 142 more
### Island 8 (130 decls)
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.casesOn`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.ctorIdx`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.mk`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.mk.inj`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.mk.noConfusion`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.noConfusion`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.noConfusionType`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.rec`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.recOn`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.support`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.BooleanWeylGroup.support_subset`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.casesOn`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.ctorIdx`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.mk`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.mk.inj`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.mk.noConfusion`
  - `InfoGeometry.Canonical.FormalPrimeRootSystem.FormalPrimeRootLattice.mk.sizeOf_spec`
  - ... and 110 more
### Island 9 (123 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.CollisionResistance_RH`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.ConformalClosure_compact`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.DiracDrazin_well_posedness`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.DrazinCore_BPS_Correspondence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.DrazinCore_zero_entropy`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.FTA_RH_topological_equivalence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Fierz_spacetime_emergence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Fierz_vector_equals_Souriau_temperature`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.MaxEnt_RH_Equivalence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.MoebiusV4_dark_matter_dark_energy_swap`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Riemann_BPS_Correspondence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.SouriauDiracDrazin_equivalence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Souriau_KMS_BPS_Correspondence`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Spire_Stability_Unification`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.Ternaform_conformal_closure`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.V4_Weyl_Isomorphism`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.V4_symmetry_forces_compactification`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.arithmetic_big_bang_is_bayesian_update`
  - `InfoGeometry.Canonical.OpenProblemFormalization.FrontierHypotheses.arithmetic_cosmological_stability`
  - ... and 103 more
### Island 10 (85 decls)
  - `InfoGeometry.LLM.ActionWeights`
  - `InfoGeometry.LLM.ActionWeights.anomaly`
  - `InfoGeometry.LLM.ActionWeights.casesOn`
  - `InfoGeometry.LLM.ActionWeights.ctorIdx`
  - `InfoGeometry.LLM.ActionWeights.defect`
  - `InfoGeometry.LLM.ActionWeights.mk`
  - `InfoGeometry.LLM.ActionWeights.mk.inj`
  - `InfoGeometry.LLM.ActionWeights.mk.noConfusion`
  - `InfoGeometry.LLM.ActionWeights.mk.sizeOf_spec`
  - `InfoGeometry.LLM.ActionWeights.noConfusion`
  - `InfoGeometry.LLM.ActionWeights.noConfusionType`
  - `InfoGeometry.LLM.ActionWeights.rec`
  - `InfoGeometry.LLM.ActionWeights.recOn`
  - `InfoGeometry.LLM.ActionWeights.regularCore`
  - `InfoGeometry.LLM.ActionWeights.repDepth`
  - `InfoGeometry.LLM.ActionWeights.transport`
  - `InfoGeometry.LLM.CompilerTelemetryShadow`
  - `InfoGeometry.LLM.CompilerTelemetryShadow.casesOn`
  - `InfoGeometry.LLM.CompilerTelemetryShadow.ctorIdx`
  - `InfoGeometry.LLM.CompilerTelemetryShadow.goalCountAfter`
  - ... and 65 more
### Island 11 (81 decls)
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.casesOn`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.ctorElim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.ctorElimType`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.ctorIdx`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.entropyProductionSecondLaw`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.entropyProductionSecondLaw.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.entropyProductionSecondLaw.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.fenchelLegendreDuality`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.fenchelLegendreDuality.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.fenchelLegendreDuality.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.hessianFisherCovariance`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.hessianFisherCovariance.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.hessianFisherCovariance.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.noConfusion`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.noConfusionType`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.ofNat`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.ofNat_ctorIdx`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.onsagerMetriplecticDissipation`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoFamily.onsagerMetriplecticDissipation.elim`
  - ... and 61 more
### Island 12 (78 decls)
  - `InfoGeometry.Meta.RepDepth`
  - `InfoGeometry.Meta.RepDepth.casesOn`
  - `InfoGeometry.Meta.RepDepth.count`
  - `InfoGeometry.Meta.RepDepth.count.elim`
  - `InfoGeometry.Meta.RepDepth.count.sizeOf_spec`
  - `InfoGeometry.Meta.RepDepth.ctorElim`
  - `InfoGeometry.Meta.RepDepth.ctorElimType`
  - `InfoGeometry.Meta.RepDepth.ctorIdx`
  - `InfoGeometry.Meta.RepDepth.exportTags`
  - `InfoGeometry.Meta.RepDepth.krein`
  - `InfoGeometry.Meta.RepDepth.krein.elim`
  - `InfoGeometry.Meta.RepDepth.krein.sizeOf_spec`
  - `InfoGeometry.Meta.RepDepth.layerDescription`
  - `InfoGeometry.Meta.RepDepth.layerLabel`
  - `InfoGeometry.Meta.RepDepth.noConfusion`
  - `InfoGeometry.Meta.RepDepth.noConfusionType`
  - `InfoGeometry.Meta.RepDepth.ofNat`
  - `InfoGeometry.Meta.RepDepth.ofNat_ctorIdx`
  - `InfoGeometry.Meta.RepDepth.operator`
  - `InfoGeometry.Meta.RepDepth.operator.elim`
  - ... and 58 more
### Island 13 (72 decls)
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.A_L`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.A_R`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.commute_LR`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.mk`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.mk.inj`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.mk.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.noConfusionType`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.rec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.recOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.BipartiteStateData.ω`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.DrazinNullCovariance`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.DrazinNullCovariance.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.DrazinNullCovariance.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.DrazinNullCovariance.leftObservable`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.DrazinNullCovariance.left_mem`
  - ... and 52 more
### Island 14 (69 decls)
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.analogy`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.analogy.elim`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.analogy.sizeOf_spec`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.casesOn`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.ctorElim`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.ctorElimType`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.ctorIdx`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.externalFact`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.externalFact.elim`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.externalFact.sizeOf_spec`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.noConfusion`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.noConfusionType`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.ofNat`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.ofNat_ctorIdx`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.rec`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.recOn`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.repoTheorem`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.repoTheorem.elim`
  - `InfoGeometry.LLM.HypothesisScaffold70.H70Authority.repoTheorem.sizeOf_spec`
  - ... and 49 more
### Island 15 (66 decls)
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.a`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.b`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.c`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.casesOn`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.ctorIdx`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.denominator`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.denominatorA_dvd_numerator`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.denominatorB_dvd_numerator`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.denominatorC_dvd_numerator`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.denominator_dvd_numerator`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.exists_quotient`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.mk`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.mk.inj`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.mk.noConfusion`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.n`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.noConfusion`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.noConfusionType`
  - `InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow.ThreeNodePolynomialShadow.numerator`
  - ... and 46 more
### Island 16 (59 decls)
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.casesOn`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.covarianceMetric`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.covarianceMetric.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.covarianceMetric.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.ctorElim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.ctorElimType`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.ctorIdx`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.entropyProduction`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.entropyProduction.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.entropyProduction.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.fisherMetric`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.fisherMetric.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.fisherMetric.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.geometricTemperature`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.geometricTemperature.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.geometricTemperature.sizeOf_spec`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.massieuPotential`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.massieuPotential.elim`
  - `InfoGeometry.Canonical.BulgarianThermodynamicGeometryPacket.BulgarianThermoSymbol.massieuPotential.sizeOf_spec`
  - ... and 39 more
### Island 17 (58 decls)
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.casesOn`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation.elim`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.chebyshevSpectralCollocation.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.ctorElim`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.ctorElimType`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.noConfusion`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.ofNat`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.ofNat_ctorIdx`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.rec`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.recOn`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.thermalMatsubaraSummation`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.thermalMatsubaraSummation.elim`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.thermalMatsubaraSummation.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.ImaginaryTimeDiscretizationScheme.toCtorIdx`
  - `InfoGeometry.SuperMetriplectic.KMSImaginaryTimeDiscretizationPolicy`
  - `InfoGeometry.SuperMetriplectic.KMSImaginaryTimeDiscretizationPolicy.analyticStripResolved`
  - ... and 38 more
### Island 18 (55 decls)
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.bridgeOwned`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.bridgeOwned.elim`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.bridgeOwned.sizeOf_spec`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.casesOn`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ctorElim`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ctorElimType`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ctorIdx`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.debt`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.debt.elim`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.debt.sizeOf_spec`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.finiteShadow`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.finiteShadow.elim`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.finiteShadow.sizeOf_spec`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.noConfusion`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.noConfusionType`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ofNat`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ofNat_ctorIdx`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ownerOwned`
  - `InfoGeometry.Canonical.TheoryShadowRepresentation.ShadowStatus.ownerOwned.elim`
  - ... and 35 more
### Island 19 (51 decls)
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.actToken`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.actToken.eq_1`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.actToken_dual`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.actToken_involutive`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.actToken_primal`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.casesOn`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.ctorIdx`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.grade`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.involutive`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.mk`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.mk.inj`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.mk.noConfusion`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.mk.sizeOf_spec`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.noConfusion`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.noConfusionType`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.rec`
  - `InfoGeometry.LLM.SpectralToken.SpectralGrading.recOn`
  - `InfoGeometry.LLM.SpectralToken.SpectralToken`
  - `InfoGeometry.LLM.SpectralToken.SpectralToken.casesOn`
  - ... and 31 more
### Island 20 (46 decls)
  - `InfoGeometry.Canonical.SpineFunctorKind`
  - `InfoGeometry.Canonical.SpineFunctorKind.casesOn`
  - `InfoGeometry.Canonical.SpineFunctorKind.constructor`
  - `InfoGeometry.Canonical.SpineFunctorKind.constructor.elim`
  - `InfoGeometry.Canonical.SpineFunctorKind.constructor.sizeOf_spec`
  - `InfoGeometry.Canonical.SpineFunctorKind.ctorElim`
  - `InfoGeometry.Canonical.SpineFunctorKind.ctorElimType`
  - `InfoGeometry.Canonical.SpineFunctorKind.ctorIdx`
  - `InfoGeometry.Canonical.SpineFunctorKind.lift`
  - `InfoGeometry.Canonical.SpineFunctorKind.lift.elim`
  - `InfoGeometry.Canonical.SpineFunctorKind.lift.sizeOf_spec`
  - `InfoGeometry.Canonical.SpineFunctorKind.noConfusion`
  - `InfoGeometry.Canonical.SpineFunctorKind.noConfusionType`
  - `InfoGeometry.Canonical.SpineFunctorKind.rec`
  - `InfoGeometry.Canonical.SpineFunctorKind.recOn`
  - `InfoGeometry.Canonical.SpineFunctorKind.responder`
  - `InfoGeometry.Canonical.SpineFunctorKind.responder.elim`
  - `InfoGeometry.Canonical.SpineFunctorKind.responder.sizeOf_spec`
  - `InfoGeometry.Canonical.SpineFunctorKind.toCtorIdx`
  - `InfoGeometry.Canonical.instBEqSpineFunctorKind`
  - ... and 26 more
### Island 21 (45 decls)
  - `InfoGeometry.Analytic.EmergentVolumeWitness`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.casesOn`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.ctorIdx`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.mk`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.mk.inj`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.mk.noConfusion`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.mk.sizeOf_spec`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.noConfusion`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.noConfusionType`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.rec`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.recOn`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.volumeMatches`
  - `InfoGeometry.Analytic.EmergentVolumeWitness.zeta`
  - `InfoGeometry.Analytic.HeatKernelWitness`
  - `InfoGeometry.Analytic.HeatKernelWitness.casesOn`
  - `InfoGeometry.Analytic.HeatKernelWitness.ctorIdx`
  - `InfoGeometry.Analytic.HeatKernelWitness.mellinBridge`
  - `InfoGeometry.Analytic.HeatKernelWitness.mk`
  - `InfoGeometry.Analytic.HeatKernelWitness.mk.inj`
  - `InfoGeometry.Analytic.HeatKernelWitness.mk.noConfusion`
  - ... and 25 more
### Island 22 (44 decls)
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.casesOn`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.ctorIdx`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.d`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.f`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.mk`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.mk.inj`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.mk.noConfusion`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.mk.sizeOf_spec`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.noConfusion`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.noConfusionType`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.rec`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ConstraintFamily.recOn`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.IsFeasible`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.Observable`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ProbDist`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ProbDist.casesOn`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ProbDist.ctorIdx`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ProbDist.mk`
  - `InfoGeometry.MaxEnt.JaynesInfoStatMech.ProbDist.mk.inj`
  - ... and 24 more
### Island 23 (44 decls)
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.HasTwoCopySYKLikeProtocol`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.casesOn`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.ctorElim`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.ctorElimType`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.ctorIdx`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.external_interpretation`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.external_interpretation.elim`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.external_interpretation.sizeOf_spec`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.formalizable_next_owner_target`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.formalizable_next_owner_target.elim`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.formalizable_next_owner_target.sizeOf_spec`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.noConfusion`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.noConfusionType`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.ofNat`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.ofNat_ctorIdx`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.rec`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.recOn`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.repo_theorem`
  - `InfoGeometry.Canonical.SYKKitaevGuardrails.ScopeBand.repo_theorem.elim`
  - ... and 24 more
### Island 24 (43 decls)
  - `InfoGeometry.SuperMetriplectic.TKKGrade`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.casesOn`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.ctorElim`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.ctorElimType`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.dual`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.dual_dual`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.minus`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.minus.elim`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.minus.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.noConfusion`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.ofNat`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.ofNat_ctorIdx`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.plus`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.plus.elim`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.plus.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.rec`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.recOn`
  - `InfoGeometry.SuperMetriplectic.TKKGrade.toCtorIdx`
  - ... and 23 more
### Island 25 (42 decls)
  - `InfoGeometry.Clifford.Cl11Matrix.Eminus`
  - `InfoGeometry.Clifford.Cl11Matrix.Eminus.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.Eminus_sq`
  - `InfoGeometry.Clifford.Cl11Matrix.Eplus`
  - `InfoGeometry.Clifford.Cl11Matrix.Eplus.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.Eplus_mul_Eminus`
  - `InfoGeometry.Clifford.Cl11Matrix.Eplus_sq`
  - `InfoGeometry.Clifford.Cl11Matrix.J1`
  - `InfoGeometry.Clifford.Cl11Matrix.J1.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.J1_cl`
  - `InfoGeometry.Clifford.Cl11Matrix.J1_cl.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.J1_sq`
  - `InfoGeometry.Clifford.Cl11Matrix.J1_transpose`
  - `InfoGeometry.Clifford.Cl11Matrix.Mat2`
  - `InfoGeometry.Clifford.Cl11Matrix.Vec11`
  - `InfoGeometry.Clifford.Cl11Matrix.alpha`
  - `InfoGeometry.Clifford.Cl11Matrix.alpha.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.beta`
  - `InfoGeometry.Clifford.Cl11Matrix.beta.eq_1`
  - `InfoGeometry.Clifford.Cl11Matrix.cl11EquivMat`
  - ... and 22 more
### Island 26 (40 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.bkmCovariance`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.bkmCovarianceWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.family`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.firstMoment`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.firstMomentFormulaWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.higherCumulantWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.nResponseForm`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.rec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.MomentGeneratingReadout.recOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.OperatorialExponentialFamily`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.OperatorialExponentialFamily.K`
  - ... and 20 more
### Island 27 (37 decls)
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.beta`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.casesOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.ctorIdx`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.inverseZetaValue`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.inverseZeta_eq_weylDenominator`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.inverseZeta_eq_weylDenominator_paritySupertrace`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.mk`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.mk.inj`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.mk.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.noConfusionType`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.paritySupertrace`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.rec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.recOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.thermalEvaluation`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.thermalEvaluationWitness`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.weylDenominatorValue`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.InverseZetaWeylParitySupertrace.weylDenominator_eq_paritySupertrace`
  - ... and 17 more
### Island 28 (34 decls)
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.afterAttention`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.attention`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.attentionNorm`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.baseUseQkNorm`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.casesOn`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.ctorIdx`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.feedForward`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.ffnNorm`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.globalMask`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.isNopeLayer`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.localMask`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.mk`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.mk.inj`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.mk.noConfusion`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.mk.sizeOf_spec`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.noConfusion`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.noConfusionType`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.rec`
  - `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.recOn`
  - ... and 14 more
### Island 29 (34 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.entropyDerivativeAtOneWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.finiteSupportVolumeWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.gamma`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.massieuAtBeta`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.massieuAtBeta_eq_log_partition`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.massieuAtGammaBeta`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.massieuAtGammaBeta_eq_log_partition`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.petzRelativeRenyi`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.petz_sandwiched_separated`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.rec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RenyiMellinSouriauReadout.recOn`
  - ... and 14 more
### Island 30 (32 decls)
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.artifactKind`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.casesOn`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.conclusionHashShapeCanonical`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.conclusionPretty`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.constName`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.ctorIdx`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.declarationKind`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.fullTypeHashShapeCanonical`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.fullTypePretty`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.kernelStatus`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.mk`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.mk.inj`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.mk.noConfusion`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.mk.sizeOf_spec`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.noConfusion`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.noConfusionType`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.rec`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.recOn`
  - `InfoGeometry.Meta.HiveLogos.FossilArtifact.space`
  - ... and 12 more
### Island 31 (31 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.Jhat`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.Khat_beta`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.Khat_beta_eq`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.Khat_beta_eq_Jhat_beta`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.beta`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.modularHamiltonian`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.modularHamiltonian_eq`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.modularHamiltonian_eq_Khat_add_logZ`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.opAdd`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.opIdentity`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.QuantumOperatorialSouriauFamily.opScale`
  - ... and 11 more
### Island 32 (31 decls)
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.mk`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.mk.inj`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.mk.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.noConfusionType`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.rec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.recOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementCriterionWitness.witness`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.certified`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.entropy`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.gaussianBosonic`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.gaussianFermionic`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.EntanglementWitness.mk`
  - ... and 11 more
### Island 33 (31 decls)
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.casesOn`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.ctorIdx`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.deformationDomain`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.mk`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.mk.inj`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.mk.noConfusion`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.noConfusion`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.noConfusionType`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.q`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.q_eq_thermalParameter`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.rec`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.recOn`
  - `InfoGeometry.Canonical.DeformationLayer.DeformationParameterWitness.thermalParameter`
  - `InfoGeometry.Canonical.DeformationLayer.DeformedCharacterWitness`
  - `InfoGeometry.Canonical.DeformationLayer.DeformedCharacterWitness.casesOn`
  - `InfoGeometry.Canonical.DeformationLayer.DeformedCharacterWitness.ctorIdx`
  - `InfoGeometry.Canonical.DeformationLayer.DeformedCharacterWitness.deformation`
  - `InfoGeometry.Canonical.DeformationLayer.DeformedCharacterWitness.deformationLaw`
  - ... and 11 more
### Island 34 (30 decls)
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.casesOn`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.ctorIdx`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.involutive`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.mk`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.mk.inj`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.mk.noConfusion`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.noConfusion`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.noConfusionType`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.rec`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.recOn`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralGrading.Γ5`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.K`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.casesOn`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.ctorIdx`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.mk`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.mk.inj`
  - `InfoGeometry.Canonical.ChiralKMSOwner.ChiralKMSFlowWitness.mk.noConfusion`
  - ... and 10 more
### Island 35 (30 decls)
  - `InfoGeometry.Thermo.Op`
  - `InfoGeometry.Thermo.ThermalModel`
  - `InfoGeometry.Thermo.ThermalModel.H`
  - `InfoGeometry.Thermo.ThermalModel.SatisfiesKMSLike`
  - `InfoGeometry.Thermo.ThermalModel.SatisfiesKMSLikeOn`
  - `InfoGeometry.Thermo.ThermalModel.casesOn`
  - `InfoGeometry.Thermo.ThermalModel.ctorIdx`
  - `InfoGeometry.Thermo.ThermalModel.densityMatrix`
  - `InfoGeometry.Thermo.ThermalModel.gibbsExpectation`
  - `InfoGeometry.Thermo.ThermalModel.gibbsWeight`
  - `InfoGeometry.Thermo.ThermalModel.gibbsWeight.eq_1`
  - `InfoGeometry.Thermo.ThermalModel.logUnnormalizedDensity`
  - `InfoGeometry.Thermo.ThermalModel.logUnnormalizedDensity.eq_1`
  - `InfoGeometry.Thermo.ThermalModel.mk`
  - `InfoGeometry.Thermo.ThermalModel.mk.inj`
  - `InfoGeometry.Thermo.ThermalModel.mk.noConfusion`
  - `InfoGeometry.Thermo.ThermalModel.mk.sizeOf_spec`
  - `InfoGeometry.Thermo.ThermalModel.modularShift`
  - `InfoGeometry.Thermo.ThermalModel.modularShiftFromLogDensity`
  - `InfoGeometry.Thermo.ThermalModel.modularShiftFromLogDensity_eq_modularShift`
  - ... and 10 more
### Island 36 (30 decls)
  - `InfoGeometry.Meta.CurvatureStats`
  - `InfoGeometry.Meta.CurvatureStats.bestContextName?`
  - `InfoGeometry.Meta.CurvatureStats.bestSharedConstCount`
  - `InfoGeometry.Meta.CurvatureStats.bestSharedContextWeight`
  - `InfoGeometry.Meta.CurvatureStats.casesOn`
  - `InfoGeometry.Meta.CurvatureStats.contextBindingCount`
  - `InfoGeometry.Meta.CurvatureStats.contextConstUnionCount`
  - `InfoGeometry.Meta.CurvatureStats.ctorIdx`
  - `InfoGeometry.Meta.CurvatureStats.exactSyntacticMatch`
  - `InfoGeometry.Meta.CurvatureStats.missingConstCount`
  - `InfoGeometry.Meta.CurvatureStats.mk`
  - `InfoGeometry.Meta.CurvatureStats.mk.inj`
  - `InfoGeometry.Meta.CurvatureStats.mk.noConfusion`
  - `InfoGeometry.Meta.CurvatureStats.mk.sizeOf_spec`
  - `InfoGeometry.Meta.CurvatureStats.noConfusion`
  - `InfoGeometry.Meta.CurvatureStats.noConfusionType`
  - `InfoGeometry.Meta.CurvatureStats.rec`
  - `InfoGeometry.Meta.CurvatureStats.recOn`
  - `InfoGeometry.Meta.CurvatureStats.targetConstCount`
  - `InfoGeometry.Meta.CurvatureStats.targetWeight`
  - ... and 10 more
### Island 37 (29 decls)
  - `InfoGeometry.Meta.DrazinRefactor.classifyLegacyUsage`
  - `InfoGeometry.Meta.DrazinRefactor.classifyLegacyUsage.match_1`
  - `InfoGeometry.Meta.DrazinRefactor.constantValue?`
  - `InfoGeometry.Meta.DrazinRefactor.constantValue?.match_1`
  - `InfoGeometry.Meta.DrazinRefactor.legacyCanonicalRieszDataName`
  - `InfoGeometry.Meta.DrazinRefactor.legacyClassicalRieszName`
  - `InfoGeometry.Meta.DrazinRefactor.legacyInfiniteAssumptionsName`
  - `InfoGeometry.Meta.DrazinRefactor.legacyPackagingTargets`
  - `InfoGeometry.Meta.DrazinRefactor.legacyProjectionTargets`
  - `InfoGeometry.Meta.DrazinRefactor.logHits`
  - `InfoGeometry.Meta.DrazinRefactor.logProjectionHits`
  - `InfoGeometry.Meta.DrazinRefactor.logProjectionHits.match_1`
  - `InfoGeometry.Meta.DrazinRefactor.nameFromDotted`
  - `InfoGeometry.Meta.DrazinRefactor.projectionLabel`
  - `InfoGeometry.Meta.DrazinRefactor.projectionLabel.match_1`
  - `InfoGeometry.Meta.DrazinRefactor.scanProjectionUsage`
  - `InfoGeometry.Meta.DrazinRefactor.scanTypes`
  - `InfoGeometry.Meta.DrazinRefactor.scanTypes.match_1`
  - `InfoGeometry.Meta.DrazinRefactor.scanValues`
  - `InfoGeometry.Meta.DrazinRefactor.scanValues.match_1`
  - ... and 9 more
### Island 38 (29 decls)
  - `InfoGeometry.Core.JordanAlgebra`
  - `InfoGeometry.Core.jordan_prod_add_left`
  - `InfoGeometry.Core.jordan_prod_add_right`
  - `InfoGeometry.Core.jordan_prod_comm`
  - `InfoGeometry.Core.jordan_prod_identity`
  - `InfoGeometry.Core.jordan_prod_smul_left`
  - `InfoGeometry.Core.jordan_prod_smul_right`
  - `InfoGeometry.Jordan.JordanAlgebra`
  - `InfoGeometry.Jordan.JordanAlgebra.add_left`
  - `InfoGeometry.Jordan.JordanAlgebra.casesOn`
  - `InfoGeometry.Jordan.JordanAlgebra.comm`
  - `InfoGeometry.Jordan.JordanAlgebra.ctorIdx`
  - `InfoGeometry.Jordan.JordanAlgebra.jordanProd`
  - `InfoGeometry.Jordan.JordanAlgebra.jordan_identity`
  - `InfoGeometry.Jordan.JordanAlgebra.mk`
  - `InfoGeometry.Jordan.JordanAlgebra.mk.noConfusion`
  - `InfoGeometry.Jordan.JordanAlgebra.noConfusion`
  - `InfoGeometry.Jordan.JordanAlgebra.noConfusionType`
  - `InfoGeometry.Jordan.JordanAlgebra.rec`
  - `InfoGeometry.Jordan.JordanAlgebra.recOn`
  - ... and 9 more
### Island 39 (28 decls)
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.beta`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.bosonTrace`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.boson_eq_zeta`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.casesOn`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.ctorIdx`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.fermionTrace`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.fermion_eq_zeta_div_zeta_two_beta`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.halfPlane_Re_gt_one`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.inverseZeta`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.mk`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.mk.inj`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.mk.noConfusion`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.noConfusion`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.noConfusionType`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.parityTrace`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.parity_eq_inverse_zeta`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.rec`
  - `InfoGeometry.Canonical.PrimeGasPartitions.InfiniteEulerProductWitness.recOn`
  - ... and 8 more
### Island 40 (28 decls)
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.casesOn`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.chiralKMSWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.conformalEquivarianceWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.ctorIdx`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.dilationWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.drazinMPAgreementWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.metricTransportCertified`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.metricTransportWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.mk`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.mk.inj`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.mk.noConfusion`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.noConfusion`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.noConfusionType`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.nullConePreservationCertified`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.nullConePreservationWitness`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.operatorSystem`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.quantizationCertified`
  - `InfoGeometry.Canonical.Cl44BridgeCandidate.Cl44BridgeCandidate.quantizationWitness`
  - ... and 8 more
### Island 41 (27 decls)
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.Collision`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.Q`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.a2_hestenes_packet`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.casesOn`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.ctorIdx`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.exists_norm_locked_pair_of_collision_of_normInvariant`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.exists_quadratic_locked_pair_of_collision`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorYX`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorYX.eq_1`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorZX`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorZX.eq_1`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorZY`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.factorZY.eq_1`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.mk`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.mk.inj`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.mk.noConfusion`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.noConfusion`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.A2HestenesChart.noConfusionType`
  - ... and 7 more
### Island 42 (26 decls)
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.beta`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.casesOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.ctorIdx`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.inverseZeta`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.inverseZeta_eq_paritySupertrace`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.inverseZeta_eq_primeIndexedWeylDenominator`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.mk`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.mk.inj`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.mk.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.noConfusionType`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.paritySupertrace`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.primeIndexedWeylDenominator`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.rec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.recOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.reciprocalBosonicPartition`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.thermalEvaluationRule`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.PrimeIndexedSouriauThermalEvaluation.zeta`
  - ... and 6 more
### Island 43 (24 decls)
  - `InfoGeometry.Meta.TacticTelemetry`
  - `InfoGeometry.Meta.TacticTelemetry.casesOn`
  - `InfoGeometry.Meta.TacticTelemetry.ctorIdx`
  - `InfoGeometry.Meta.TacticTelemetry.deltaGamma`
  - `InfoGeometry.Meta.TacticTelemetry.deltaM`
  - `InfoGeometry.Meta.TacticTelemetry.dissipativeShadow`
  - `InfoGeometry.Meta.TacticTelemetry.gammaAfter`
  - `InfoGeometry.Meta.TacticTelemetry.gammaBefore`
  - `InfoGeometry.Meta.TacticTelemetry.goalAfter`
  - `InfoGeometry.Meta.TacticTelemetry.goalBefore`
  - `InfoGeometry.Meta.TacticTelemetry.mAfter`
  - `InfoGeometry.Meta.TacticTelemetry.mBefore`
  - `InfoGeometry.Meta.TacticTelemetry.mk`
  - `InfoGeometry.Meta.TacticTelemetry.mk.inj`
  - `InfoGeometry.Meta.TacticTelemetry.mk.noConfusion`
  - `InfoGeometry.Meta.TacticTelemetry.mk.sizeOf_spec`
  - `InfoGeometry.Meta.TacticTelemetry.noConfusion`
  - `InfoGeometry.Meta.TacticTelemetry.noConfusionType`
  - `InfoGeometry.Meta.TacticTelemetry.phaseShadow`
  - `InfoGeometry.Meta.TacticTelemetry.rec`
  - ... and 4 more
### Island 44 (24 decls)
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.cartanLift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.cartanLift_proof`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.casesOn`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.defectLift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.defectLift_proof`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.exchangeLift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.exchangeLift_proof`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.flowLift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.flowLift_proof`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.global_lift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.leftLift`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.leftLift_proof`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.mk`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.mk.inj`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.mk.noConfusion`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.mk.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.noConfusion`
  - `InfoGeometry.SuperMetriplectic.BlockwiseOperatorLiftObligations.noConfusionType`
  - ... and 4 more
### Island 45 (23 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GENERICCompatibility`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.K`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.K_deltaE_eq_zero`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.K_symmetric_psd`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.L`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.L_deltaS_eq_zero`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.L_skew_poisson`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.dE_eq_zero`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.dE_eq_zero_and_dS_nonneg`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.dS_nonneg`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.energy`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.entropy`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.GenericMetriplecticCompatibility.noConfusion`
  - ... and 3 more
### Island 46 (22 decls)
  - `InfoGeometry.Clifford.Cl11Quaternion.Cl11`
  - `InfoGeometry.Clifford.Cl11Quaternion.Hsplit`
  - `InfoGeometry.Clifford.Cl11Quaternion.Mat₂`
  - `InfoGeometry.Clifford.Cl11Quaternion.Q11`
  - `InfoGeometry.Clifford.Cl11Quaternion.cliffordEquivMat`
  - `InfoGeometry.Clifford.Cl11Quaternion.iM`
  - `InfoGeometry.Clifford.Cl11Quaternion.iM.eq_1`
  - `InfoGeometry.Clifford.Cl11Quaternion.jM`
  - `InfoGeometry.Clifford.Cl11Quaternion.jM.eq_1`
  - `InfoGeometry.Clifford.Cl11Quaternion.kM`
  - `InfoGeometry.Clifford.Cl11Quaternion.kM.eq_1`
  - `InfoGeometry.Clifford.Cl11Quaternion.kM_eq`
  - `InfoGeometry.Clifford.Cl11Quaternion.matBasis`
  - `InfoGeometry.Clifford.Cl11Quaternion.matBasis.eq_1`
  - `InfoGeometry.Clifford.Cl11Quaternion.ofMatrix`
  - `InfoGeometry.Clifford.Cl11Quaternion.ofMatrix.eq_1`
  - `InfoGeometry.Clifford.Cl11Quaternion.ofMatrix_toMatrix`
  - `InfoGeometry.Clifford.Cl11Quaternion.quatEquivMat`
  - `InfoGeometry.Clifford.Cl11Quaternion.toMatrix`
  - `InfoGeometry.Clifford.Cl11Quaternion.toMatrix.eq_1`
  - ... and 2 more
### Island 47 (22 decls)
  - `InfoGeometry.Architecture.SpinFactor.SpinFactorDomain`
  - `InfoGeometry.Architecture.SpinFactor.spinFactorPotential`
  - `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_well_defined`
  - `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_zero`
  - `InfoGeometry.Convex.SpinFactorHessian.spinFactor_radon_nikodym_entropy`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.casesOn`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.cramer_rao_floor`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.ctorIdx`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.domain_valid`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.mk`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.mk.inj`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.mk.noConfusion`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.mk.sizeOf_spec`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.noConfusion`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.noConfusionType`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.rec`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.recOn`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.variance_limit`
  - `InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.x`
  - ... and 2 more
### Island 48 (22 decls)
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.Q`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.casesOn`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.ctorIdx`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.factor`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.factor_eq_zero_iff`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.factor_ne_zero_iff`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.mk`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.mk.inj`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.mk.noConfusion`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.noConfusion`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.noConfusionType`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.norm_eq_of_collision_of_normInvariant`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.quadratic`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.quadraticInvariant`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.quadratic_eq_of_collision`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.rec`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.recOn`
  - `InfoGeometry.Canonical.HestenesQVandermondeShadow.TwoNodeHestenesChart.two_node_hestenes_packet`
  - ... and 2 more
### Island 49 (21 decls)
  - `InfoGeometry.Algebra.PrimeA1RootSystem`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.P`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.WeylGroup`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.all_prime`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.casesOn`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.ctorIdx`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.mk`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.mk.inj`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.mk.noConfusion`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.mk.sizeOf_spec`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.noConfusion`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.noConfusionType`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.rec`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.recOn`
  - `InfoGeometry.Algebra.PrimeA1RootSystem.signature`
  - `InfoGeometry.Algebra.WeylDenominator.finiteWeylDenominator`
  - `InfoGeometry.Algebra.WeylDenominator.weyl_denominator_expansion`
  - `InfoGeometry.Arithmetic.weylToNat`
  - `InfoGeometry.Arithmetic.weyl_sign_eq_moebius`
  - `InfoGeometry.Arithmetic.weyl_toNat_squarefree`
  - ... and 1 more
### Island 50 (21 decls)
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.UnitPhase`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.casesOn`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.ctorIdx`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.denominator`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.denominator.eq_1`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.denominator_eq_zero_iff`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.denominator_ne_zero_iff`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.mk`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.mk.inj`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.mk.noConfusion`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.noConfusion`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.noConfusionType`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.norm_eq_of_unitPhase_of_collision`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.q`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.rec`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.recOn`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.two_node_phase_lock_packet`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.TwoNodeQChart.x`
  - ... and 1 more
### Island 51 (20 decls)
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.UnitPhase`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.a2_phase_lock_packet`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.casesOn`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.ctorIdx`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.denominatorFactor`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.denominatorFactor_eq_zero_iff`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.exists_norm_locked_pair_of_unitPhase_of_collision`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.mk`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.mk.inj`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.mk.noConfusion`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.noConfusion`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.noConfusionType`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.q`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.rec`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.recOn`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.x`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.y`
  - `InfoGeometry.Canonical.QVandermondePhaseLockShadow.A2QChart.z`
### Island 52 (20 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.densityOperator`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.gibbsFormulaWitness`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.gibbsHamiltonian`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.logPartitionScalar`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.modularHamiltonian`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.modularHamiltonian_eq_negativeLogDensity`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.modularHamiltonian_eq_negativeLogDensity_theorem`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.negativeLogDensity`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.rec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.recOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.ModularHamiltonianData.relativeModularWitness`
### Island 53 (19 decls)
  - `InfoGeometry.LLM.GatedFeedForward`
  - `InfoGeometry.LLM.GatedFeedForward.activate`
  - `InfoGeometry.LLM.GatedFeedForward.casesOn`
  - `InfoGeometry.LLM.GatedFeedForward.combine`
  - `InfoGeometry.LLM.GatedFeedForward.ctorIdx`
  - `InfoGeometry.LLM.GatedFeedForward.downProj`
  - `InfoGeometry.LLM.GatedFeedForward.gateProj`
  - `InfoGeometry.LLM.GatedFeedForward.mk`
  - `InfoGeometry.LLM.GatedFeedForward.mk.inj`
  - `InfoGeometry.LLM.GatedFeedForward.mk.noConfusion`
  - `InfoGeometry.LLM.GatedFeedForward.mk.sizeOf_spec`
  - `InfoGeometry.LLM.GatedFeedForward.noConfusion`
  - `InfoGeometry.LLM.GatedFeedForward.noConfusionType`
  - `InfoGeometry.LLM.GatedFeedForward.preDown`
  - `InfoGeometry.LLM.GatedFeedForward.rec`
  - `InfoGeometry.LLM.GatedFeedForward.recOn`
  - `InfoGeometry.LLM.GatedFeedForward.run`
  - `InfoGeometry.LLM.GatedFeedForward.run_def`
  - `InfoGeometry.LLM.GatedFeedForward.upProj`
### Island 54 (19 decls)
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.algebraic_equilibrium_packet`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.casesOn`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.ctorIdx`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.fisherMetric_nonneg`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.kmsEquilibrium`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.mk`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.mk.inj`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.noConfusion`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.noConfusionType`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.quantumFisherMetric`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.quantumFisherMetric_nonneg`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.rec`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.recOn`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.souriauMomentGenerator`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.state`
  - `InfoGeometry.Canonical.SouriauLieThermoKKTBridge.CoordinatelessKMSFisherState.weylAutomorphismInvariant`
### Island 55 (19 decls)
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.bulkViscosity`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.bulkViscosity_eq_zero_of_anomaly_zero`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.bulkViscosity_eq_zero_of_conformal_trace_zero`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.bulkViscosity_eq_zero_of_trace_zero`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.casesOn`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.conformalAnomaly`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.mk`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.mk.inj`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.mk.noConfusion`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.mk.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.noConfusion`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.rec`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.recOn`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.traceStress`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.trace_eq`
  - `InfoGeometry.SuperMetriplectic.ConformalBulkViscosityPacket.trace_eq_anomaly`
### Island 56 (19 decls)
  - `InfoGeometry.LLM.KVCache`
  - `InfoGeometry.LLM.KVCache.casesOn`
  - `InfoGeometry.LLM.KVCache.ctorIdx`
  - `InfoGeometry.LLM.KVCache.keyAt`
  - `InfoGeometry.LLM.KVCache.keyAt_write_ne`
  - `InfoGeometry.LLM.KVCache.keyAt_write_same`
  - `InfoGeometry.LLM.KVCache.mk`
  - `InfoGeometry.LLM.KVCache.mk.inj`
  - `InfoGeometry.LLM.KVCache.mk.noConfusion`
  - `InfoGeometry.LLM.KVCache.mk.sizeOf_spec`
  - `InfoGeometry.LLM.KVCache.noConfusion`
  - `InfoGeometry.LLM.KVCache.noConfusionType`
  - `InfoGeometry.LLM.KVCache.rec`
  - `InfoGeometry.LLM.KVCache.recOn`
  - `InfoGeometry.LLM.KVCache.valueAt`
  - `InfoGeometry.LLM.KVCache.valueAt_write_ne`
  - `InfoGeometry.LLM.KVCache.valueAt_write_same`
  - `InfoGeometry.LLM.KVCache.write`
  - `InfoGeometry.LLM.KVCache.write.eq_1`
### Island 57 (18 decls)
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.Mat2`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearA`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearA.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearAprime`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearAprime.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearCounterexample_Aprime_eq`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearCounterexample_drazin_ne_euclideanMP`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearCounterexample_fixedMetric_MP_transport_fails`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearDrazinZeroAprime`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearDrazinZeroAprime.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearEuclideanMPZeroA`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearEuclideanMPZeroA.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearEuclideanMPZeroAprime`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearEuclideanMPZeroAprime.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearG`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearG.eq_1`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearGInv`
  - `InfoGeometry.Canonical.ConformalProjectorAgreement.shearGInv.eq_1`
### Island 58 (18 decls)
  - `InfoGeometry.Canonical.QuantumInference.CCR`
  - `InfoGeometry.Canonical.QuantumInference.CCR.a`
  - `InfoGeometry.Canonical.QuantumInference.CCR.adag`
  - `InfoGeometry.Canonical.QuantumInference.CCR.casesOn`
  - `InfoGeometry.Canonical.QuantumInference.CCR.comm_a_a`
  - `InfoGeometry.Canonical.QuantumInference.CCR.comm_a_adag`
  - `InfoGeometry.Canonical.QuantumInference.CCR.comm_adag_adag`
  - `InfoGeometry.Canonical.QuantumInference.CCR.ctorIdx`
  - `InfoGeometry.Canonical.QuantumInference.CCR.hessian_indefinite_form`
  - `InfoGeometry.Canonical.QuantumInference.CCR.mk`
  - `InfoGeometry.Canonical.QuantumInference.CCR.mk.inj`
  - `InfoGeometry.Canonical.QuantumInference.CCR.mk.noConfusion`
  - `InfoGeometry.Canonical.QuantumInference.CCR.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.QuantumInference.CCR.noConfusion`
  - `InfoGeometry.Canonical.QuantumInference.CCR.noConfusionType`
  - `InfoGeometry.Canonical.QuantumInference.CCR.rec`
  - `InfoGeometry.Canonical.QuantumInference.CCR.recOn`
  - `InfoGeometry.Canonical.QuantumInference.comm`
### Island 59 (18 decls)
  - `InfoGeometry.MaxEnt.BurgModel`
  - `InfoGeometry.MaxEnt.BurgModel.casesOn`
  - `InfoGeometry.MaxEnt.BurgModel.coeff`
  - `InfoGeometry.MaxEnt.BurgModel.ctorIdx`
  - `InfoGeometry.MaxEnt.BurgModel.mk`
  - `InfoGeometry.MaxEnt.BurgModel.mk.inj`
  - `InfoGeometry.MaxEnt.BurgModel.mk.noConfusion`
  - `InfoGeometry.MaxEnt.BurgModel.mk.sizeOf_spec`
  - `InfoGeometry.MaxEnt.BurgModel.noConfusion`
  - `InfoGeometry.MaxEnt.BurgModel.noConfusionType`
  - `InfoGeometry.MaxEnt.BurgModel.noiseVar`
  - `InfoGeometry.MaxEnt.BurgModel.noiseVar_nonneg`
  - `InfoGeometry.MaxEnt.BurgModel.rec`
  - `InfoGeometry.MaxEnt.BurgModel.recOn`
  - `InfoGeometry.MaxEnt.BurgModel.spectrum`
  - `InfoGeometry.MaxEnt.BurgModel.spectrum_nonneg`
  - `InfoGeometry.MaxEnt.arSpectralDensity`
  - `InfoGeometry.MaxEnt.arSpectralDensity_nonneg`
### Island 60 (17 decls)
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.crossCorrelation`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.factorsThrough`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.mk`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.mk.inj`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.mk.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.noConfusionType`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.rec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.recOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.residualMismatch`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.transfer`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.ResidualCorrelationThroughMismatch.transfer_zero`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.mismatch_zero_kills_correlation`
### Island 61 (17 decls)
  - `InfoGeometry.Causal.CausalStructure`
  - `InfoGeometry.Causal.CausalStructure.Boundary`
  - `InfoGeometry.Causal.CausalStructure.Boundary.eq_1`
  - `InfoGeometry.Causal.CausalStructure.Interior`
  - `InfoGeometry.Causal.CausalStructure.Interior.eq_1`
  - `InfoGeometry.Causal.CausalStructure.Q`
  - `InfoGeometry.Causal.CausalStructure.casesOn`
  - `InfoGeometry.Causal.CausalStructure.ctorIdx`
  - `InfoGeometry.Causal.CausalStructure.interior_is_non_null`
  - `InfoGeometry.Causal.CausalStructure.mk`
  - `InfoGeometry.Causal.CausalStructure.mk.inj`
  - `InfoGeometry.Causal.CausalStructure.mk.noConfusion`
  - `InfoGeometry.Causal.CausalStructure.mk.sizeOf_spec`
  - `InfoGeometry.Causal.CausalStructure.noConfusion`
  - `InfoGeometry.Causal.CausalStructure.noConfusionType`
  - `InfoGeometry.Causal.CausalStructure.rec`
  - `InfoGeometry.Causal.CausalStructure.recOn`
### Island 62 (17 decls)
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.casesOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.ctorIdx`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.entropyReadoutRequiresState`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.jacobian`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.logDetReg`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.mk`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.mk.inj`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.noConfusion`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.noConfusionType`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.rec`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.recOn`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.volumeCompressionPotential`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.volumeCompressionPotential_eq_neg_logDetReg`
  - `InfoGeometry.Canonical.SouriauOperatorialLogPotential.RegularizedJacobianPotential.volumeCompressionPotential_eq_neg_logDetReg_apply`
### Island 63 (16 decls)
  - `InfoGeometry.LLM.BogoliubovTransform`
  - `InfoGeometry.LLM.BogoliubovTransform.casesOn`
  - `InfoGeometry.LLM.BogoliubovTransform.ctorIdx`
  - `InfoGeometry.LLM.BogoliubovTransform.forwardPair`
  - `InfoGeometry.LLM.BogoliubovTransform.forwardPair_fst`
  - `InfoGeometry.LLM.BogoliubovTransform.forwardPair_snd`
  - `InfoGeometry.LLM.BogoliubovTransform.hole`
  - `InfoGeometry.LLM.BogoliubovTransform.mk`
  - `InfoGeometry.LLM.BogoliubovTransform.mk.inj`
  - `InfoGeometry.LLM.BogoliubovTransform.mk.noConfusion`
  - `InfoGeometry.LLM.BogoliubovTransform.mk.sizeOf_spec`
  - `InfoGeometry.LLM.BogoliubovTransform.noConfusion`
  - `InfoGeometry.LLM.BogoliubovTransform.noConfusionType`
  - `InfoGeometry.LLM.BogoliubovTransform.particle`
  - `InfoGeometry.LLM.BogoliubovTransform.rec`
  - `InfoGeometry.LLM.BogoliubovTransform.recOn`
### Island 64 (16 decls)
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.actionAt`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.actionAt_eq_pairing`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.casesOn`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.ctorIdx`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.geometricTemperature`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.mk`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.mk.inj`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.mk.noConfusion`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.moment`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.noConfusion`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.noConfusionType`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.pairing`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.rec`
  - `InfoGeometry.Canonical.SouriauFenchelOnsagerBridge.CoadjointMomentMapData.recOn`
### Island 65 (16 decls)
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.casesOn`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.factor`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.mk`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.mk.inj`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.mk.noConfusion`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.mk.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.newEntry`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.new_eq`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.new_eq_factor_mul_old`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.noConfusion`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.oldEntry`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.rec`
  - `InfoGeometry.SuperMetriplectic.WeylScaledOnsagerEntry.recOn`
### Island 66 (16 decls)
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.beta`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.bosonicPartition`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.casesOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.ctorIdx`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.mk`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.mk.inj`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.mk.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.noConfusion`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.noConfusionType`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.rec`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.recOn`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.zetaValue`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.zeta_eq_reciprocal_bosonic_partition`
  - `InfoGeometry.Canonical.WeylCharacterEquivalence.BosonicZetaPartitionReciprocal.zeta_mul_bosonicPartition`
### Island 67 (16 decls)
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.casesOn`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.ctorIdx`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.mk`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.mk.inj`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.mk.noConfusion`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.modularHamiltonian`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.modularHamiltonian_eq_negativeLog`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.modularHamiltonian_eq_supplied_negativeLog`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.modularOperator`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.negativeLogModularOperator`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.noConfusion`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.noConfusionType`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.rec`
  - `InfoGeometry.Canonical.ModularSurprisalThermoPacket.ModularHamiltonianSurprisalContext.recOn`
### Island 68 (16 decls)
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.casesOn`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.covariance`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.ctorIdx`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.hessianEntry`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.hessian_eq`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.hessian_eq_covariance_add_cocycle`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.mk`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.mk.inj`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.mk.noConfusion`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.mk.sizeOf_spec`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.noConfusion`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.noConfusionType`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.rec`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.recOn`
  - `InfoGeometry.SuperMetriplectic.CocycleModifiedHessianEntry.souriauCocycle`
### Island 69 (15 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.self_dual_cone_equals_inner_dual`
  - `InfoGeometry.Convex.SelfDualCone`
  - `InfoGeometry.Convex.SelfDualCone.casesOn`
  - `InfoGeometry.Convex.SelfDualCone.cone`
  - `InfoGeometry.Convex.SelfDualCone.ctorIdx`
  - `InfoGeometry.Convex.SelfDualCone.innerDual_eq`
  - `InfoGeometry.Convex.SelfDualCone.mk`
  - `InfoGeometry.Convex.SelfDualCone.mk.inj`
  - `InfoGeometry.Convex.SelfDualCone.mk.noConfusion`
  - `InfoGeometry.Convex.SelfDualCone.mk.sizeOf_spec`
  - `InfoGeometry.Convex.SelfDualCone.noConfusion`
  - `InfoGeometry.Convex.SelfDualCone.noConfusionType`
  - `InfoGeometry.Convex.SelfDualCone.rec`
  - `InfoGeometry.Convex.SelfDualCone.recOn`
  - `InfoGeometry.Convex.SelfDualCone.self_dual`
### Island 70 (15 decls)
  - `InfoGeometry.Convex.OneD.IsKernelClosed`
  - `InfoGeometry.Convex.OneD.IsKernelClosed.eq_1`
  - `InfoGeometry.Convex.OneD.KernelClosedFunctions`
  - `InfoGeometry.Convex.OneD.KernelClosure`
  - `InfoGeometry.Convex.OneD.KernelClosure.eq_1`
  - `InfoGeometry.Convex.OneD.KernelClosureOperator`
  - `InfoGeometry.Convex.OneD.KernelClosureOperator.eq_1`
  - `InfoGeometry.Convex.OneD.KernelOp`
  - `InfoGeometry.Convex.OneD.KernelOp.eq_1`
  - `InfoGeometry.Convex.OneD.kernelClosedFunctionsCompleteLattice`
  - `InfoGeometry.Convex.OneD.kernelClosure_monotone`
  - `InfoGeometry.Convex.OneD.kernelOp_eq_transpose`
  - `InfoGeometry.Convex.OneD.kernelOp_monotone`
  - `InfoGeometry.Convex.OneD.kernel_idempotent`
  - `InfoGeometry.Convex.OneD.kernel_le_closure`
### Island 71 (14 decls)
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.casesOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.ctorIdx`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.mk`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.mk.inj`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.mk.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.noConfusion`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.noConfusionType`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.rec`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.recOn`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.GaussianCovarianceOwner.restrictedCovariance`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.HasDrazinNullSupportedGaussianCovariance`
  - `InfoGeometry.Canonical.EntanglementResidualOwner.restrictedCovariance_zero_implies_no_support`
### Island 72 (14 decls)
  - `InfoGeometry.Canonical.ChiralCharges`
  - `InfoGeometry.Canonical.ChiralCharges.casesOn`
  - `InfoGeometry.Canonical.ChiralCharges.ctorIdx`
  - `InfoGeometry.Canonical.ChiralCharges.minus`
  - `InfoGeometry.Canonical.ChiralCharges.mk`
  - `InfoGeometry.Canonical.ChiralCharges.mk.inj`
  - `InfoGeometry.Canonical.ChiralCharges.mk.noConfusion`
  - `InfoGeometry.Canonical.ChiralCharges.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.ChiralCharges.noConfusion`
  - `InfoGeometry.Canonical.ChiralCharges.noConfusionType`
  - `InfoGeometry.Canonical.ChiralCharges.plus`
  - `InfoGeometry.Canonical.ChiralCharges.rec`
  - `InfoGeometry.Canonical.ChiralCharges.recOn`
  - `InfoGeometry.Canonical.netChiralCharge`
### Island 73 (14 decls)
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.casesOn`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.ctorIdx`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.evaluate`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.evaluate_def`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.mk`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.mk.inj`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.mk.noConfusion`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.mk.sizeOf_spec`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.noConfusion`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.noConfusionType`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.pair`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.rec`
  - `InfoGeometry.LLM.SpectralToken.QKVTrialityCarrier.recOn`
### Island 74 (14 decls)
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.casesOn`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.ctorIdx`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.isNegative`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.isPositive`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.mk`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.mk.inj`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.mk.noConfusion`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.mk.sizeOf_spec`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.noConfusion`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.noConfusionType`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.rec`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.recOn`
  - `InfoGeometry.Canonical.SignedParticleBridge.SignedContribution.sign`
### Island 75 (13 decls)
  - `InfoGeometry.Canonical.Determinant.GL`
  - `InfoGeometry.Canonical.Determinant.detHom`
  - `InfoGeometry.Canonical.Determinant.jacDet`
  - `InfoGeometry.Canonical.Determinant.jac_det_comp`
  - `InfoGeometry.Canonical.Determinant.logAbsDet`
  - `InfoGeometry.Canonical.Determinant.logAbsDet_mul`
  - `InfoGeometry.Canonical.Determinant.range_toGL_eq_preimage_one`
  - `InfoGeometry.Canonical.Determinant.zetaRegularizedDet`
  - `InfoGeometry.Canonical.Determinant.zetaRegularizedDet_pos`
  - `InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet`
  - `InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_eq_logAbsDet`
  - `InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_mul`
  - `InfoGeometry.Canonical.RNDeterminantConnesChainBridge.jacobianDeterminant_chain`
### Island 76 (11 decls)
  - `InfoGeometry.Convex.DualSpace`
  - `InfoGeometry.Convex.dualPair`
  - `InfoGeometry.Convex.fenchelConj`
  - `InfoGeometry.Convex.fenchelConj.eq_1`
  - `InfoGeometry.Convex.fenchelConj_eq_of_isGreatest`
  - `InfoGeometry.Convex.fenchelConj_ge_eval_sub`
  - `InfoGeometry.Convex.fenchelSet`
  - `InfoGeometry.Convex.fenchelSet_nonempty`
  - `InfoGeometry.Convex.fenchelYoung`
  - `InfoGeometry.Convex.fenchelYoung_eq_of_conj_eq`
  - `InfoGeometry.Convex.le_fenchelConj`
### Island 77 (9 decls)
  - `InfoGeometry.Geometry.ConvexOn.eGeodesicConvex`
  - `InfoGeometry.Geometry.convexOn_univ_iff_eGeodesicConvex`
  - `InfoGeometry.Geometry.convex_iff_eGeodesicConvex`
  - `InfoGeometry.Geometry.eGeodesic`
  - `InfoGeometry.Geometry.eGeodesic.eq_1`
  - `InfoGeometry.Geometry.eGeodesicConvex`
  - `InfoGeometry.Geometry.eGeodesicConvex.convexOn_univ`
  - `InfoGeometry.Geometry.eGeodesic_one`
  - `InfoGeometry.Geometry.eGeodesic_zero`
### Island 78 (8 decls)
  - `InfoGeometry.cramerRateOn`
  - `InfoGeometry.cramerRateOn.congr_simp`
  - `InfoGeometry.cramerRateOn_eq_of_mem_and_max`
  - `InfoGeometry.cramerRateOn_singleton`
  - `InfoGeometry.exists_argmax_cramerRateOn`
  - `InfoGeometry.exists_mem_eq_cramerRateOn`
  - `InfoGeometry.fenchelYoung_on_cramerRateOn`
  - `InfoGeometry.le_cramerRateOn`
### Island 79 (8 decls)
  - `InfoGeometry.Canonical.ManifoldDegree.degree_change_of_variables_formula`
  - `InfoGeometry.Canonical.ManifoldDegree.localDegreeSign`
  - `InfoGeometry.Canonical.ManifoldDegree.mappingDegree`
  - `InfoGeometry.Canonical.ManifoldDegree.regularValue_of_nonvanishing_jacobian`
  - `InfoGeometry.Canonical.ManifoldHomology.IsRegularValue`
  - `InfoGeometry.Canonical.ManifoldHomology.localDegreeSign`
  - `InfoGeometry.Canonical.ManifoldHomology.mappingDegree`
  - `InfoGeometry.Canonical.ManifoldHomology.mappingDegree_eq_sum_localDegreeSign`
### Island 80 (7 decls)
  - `InfoGeometry.SLT.condExpExcept`
  - `InfoGeometry.SLT.condExpExcept.eq_1`
  - `InfoGeometry.SLT.condVarExcept`
  - `InfoGeometry.SLT.condVarExcept.eq_1`
  - `InfoGeometry.SLT.measurableSpaceExcept`
  - `InfoGeometry.SLT.setIntegral_condVarExcept_eq`
  - `InfoGeometry.SLT.setIntegral_condVar_except_eq`
### Island 81 (6 decls)
  - `InfoGeometry.Canonical.DIIIIndexVerification.mvarZ2Index`
  - `InfoGeometry.Canonical.DIIIIndexVerification.mvarZ2Index_pair_stable_from_counts`
  - `InfoGeometry.Canonical.DIIIIndexVerification.tacticStepZ2Index`
  - `InfoGeometry.Canonical.DIIIIndexVerification.z2IndexOfCount`
  - `InfoGeometry.Canonical.DIIIIndexVerification.z2IndexOfCount_val_eq_mod`
  - `InfoGeometry.Canonical.DIIIIndexVerification.z2Index_pair_stable`
### Island 82 (6 decls)
  - `InfoGeometry.Measure.MeasureRay`
  - `InfoGeometry.Measure.SameRay`
  - `InfoGeometry.Measure.SameRay.refl`
  - `InfoGeometry.Measure.SameRay.symm`
  - `InfoGeometry.Measure.SameRay.trans`
  - `InfoGeometry.Measure.instSetoidMeasure_infoGeometry`
### Island 83 (5 decls)
  - `InfoGeometry.Canonical.GrandSynthesis.jacDetCLM`
  - `InfoGeometry.Canonical.GrandSynthesis.jacDetCLM.eq_1`
  - `InfoGeometry.Canonical.GrandSynthesis.jacDetCLM_comp`
  - `InfoGeometry.Canonical.GrandSynthesis.logAbsJacDetCLM`
  - `InfoGeometry.Canonical.GrandSynthesis.logAbsJacDetCLM_comp`
### Island 84 (4 decls)
  - `InfoGeometry.Canonical.LLN.empirical_to_theoretical_slln`
  - `InfoGeometry.Canonical.LLN.fixed_partition_slln`
  - `InfoGeometry.Canonical.LLN.fixed_partition_slln.eq_1`
  - `InfoGeometry.Canonical.LLN.fixed_partition_slln_holds`
### Island 85 (4 decls)
  - `InfoGeometry.Projective.Unnormalized`
  - `InfoGeometry.Projective.ray`
  - `InfoGeometry.Projective.ray_smul`
  - `InfoGeometry.Projective.ray_smul₀`
### Island 86 (4 decls)
  - `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.IsCriticalDensityWeight`
  - `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_half`
  - `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_one`
  - `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_zero`
### Island 87 (3 decls)
  - `InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix`
  - `InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_kronecker`
  - `InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_mul`
### Island 88 (3 decls)
  - `InfoGeometry.Canonical.FUSION.ExactHessian`
  - `InfoGeometry.Canonical.FUSION.IsResolvable`
  - `InfoGeometry.Canonical.FUSION.phase_transition_catastrophe`
### Island 89 (3 decls)
  - `InfoGeometry.Canonical.RiemannResonator.IsJaynesBalanced`
  - `InfoGeometry.Canonical.RiemannResonator.riemann_hypothesis_iff_jaynes_balanced`
  - `InfoGeometry.Canonical.RiemannResonator.spectralEntropyDissipation`
### Island 90 (3 decls)
  - `InfoGeometry.MaxEnt.entropyBand_of_mem_confidenceInterval`
  - `InfoGeometry.MaxEnt.entropyConfidenceInterval`
  - `InfoGeometry.MaxEnt.mem_confidenceInterval_of_entropyBand`
### Island 91 (3 decls)
  - `InfoGeometry.Convex.euclidean_grad_monotone`
  - `InfoGeometry.Convex.grad`
  - `InfoGeometry.Convex.grad.eq_1`
### Island 92 (3 decls)
  - `InfoGeometry.Canonical.MeasureScaleShape.generalizedKL`
  - `InfoGeometry.Canonical.MeasureScaleShape.generalizedKL_scale_shape_split`
  - `InfoGeometry.Canonical.MeasureScaleShape.scalarGKL`
### Island 93 (2 decls)
  - `InfoGeometry.Meta.moduleNameOf`
  - `InfoGeometry.Meta.moduleNameOf.match_1`
### Island 94 (2 decls)
  - `InfoGeometry.Meta.isAuditableDecl`
  - `InfoGeometry.Meta.isAuditableDecl.match_1`
### Island 95 (2 decls)
  - `InfoGeometry.Quantum.ModularAnomaly.Lattice.thermalBerezinianEval`
  - `InfoGeometry.Quantum.ModularAnomaly.Lattice.thermal_berezinian_index`
### Island 96 (2 decls)
  - `InfoGeometry.Canonical.LLN.ae_tendsto_ratio_to_rnDeriv`
  - `InfoGeometry.Canonical.LLN.ae_tendsto_ratio_to_rnDeriv_holds`
### Island 97 (2 decls)
  - `InfoGeometry.Singular.Drazin.IsNormal`
  - `InfoGeometry.Singular.DrazinAdjoint.IsNormal`
### Island 98 (2 decls)
  - `InfoGeometry.TransformationGroups.location_invariant`
  - `InfoGeometry.TransformationGroups.location_invariant_const`
### Island 99 (2 decls)
  - `InfoGeometry.Meta.constantKindLabel`
  - `InfoGeometry.Meta.constantKindLabel.match_1`
### Island 100 (2 decls)
  - `InfoGeometry.TransformationGroups.scale_invariant`
  - `InfoGeometry.TransformationGroups.scale_invariant_inv`
### Island 101 (1 decls)
  - `InfoGeometry.Convex.helly_theorem'`
### Island 102 (1 decls)
  - `InfoGeometry.Canonical.WeylEquivalence.mobius_eq_weyl_signature`
### Island 103 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.finite_group_orbits_are_finite`
### Island 104 (1 decls)
  - `InfoGeometry.Measure.RadonNikodymNormalForms.lebesgueDecomposition_normalForm`
### Island 105 (1 decls)
  - `InfoGeometry.Measure.RadonNikodymNormalForms.normalForm_of_absolutelyContinuous`
### Island 106 (1 decls)
  - `InfoGeometry.MaxEnt.expectedAffineDimension`
### Island 107 (1 decls)
  - `InfoGeometry.Measure.RadonNikodymNormalForms.rnDeriv_withDensity_eq_ae`
### Island 108 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_set`
### Island 109 (1 decls)
  - `InfoGeometry.Measure.RadonNikodymNormalForms.absolutelyContinuous_iff_normalForm`
### Island 110 (1 decls)
  - `InfoGeometry.Convex.ConeRay`
### Island 111 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_set_compact`
### Island 112 (1 decls)
  - `InfoGeometry.ConvexDuality.fenchelGap`
### Island 113 (1 decls)
  - `InfoGeometry.Canonical.spineFunctorRoleTagNames`
### Island 114 (1 decls)
  - `InfoGeometry.Convex.helly_theorem`
### Island 115 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.parity_time_product_is_involution`
### Island 116 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.time_reversal_is_involution`
### Island 117 (1 decls)
  - `InfoGeometry.Meta.vacuityRoleTagNames`
### Island 118 (1 decls)
  - `InfoGeometry.Measure.RadonNikodymNormalForms.density_unique_ae`
### Island 119 (1 decls)
  - `InfoGeometry.Krein.K_comp_J_of_relations`
### Island 120 (1 decls)
  - `InfoGeometry.Canonical.HeadTrialityCore.blocked128_dimension`
### Island 121 (1 decls)
  - `InfoGeometry.Convex.ConeInteriorRay`
### Island 122 (1 decls)
  - `InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem.InformationLieAlgebra`
### Island 123 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_compact`
### Island 124 (1 decls)
  - `InfoGeometry.Convex.SpinFactorHessian.spinFactorHessian_pos_def_at_origin`
### Island 125 (1 decls)
  - `InfoGeometry.TransformationGroups.log_coord_flat`
### Island 126 (1 decls)
  - `InfoGeometry.ExponentialFamily.Class.density_pos`
### Island 127 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_set'`
### Island 128 (1 decls)
  - `InfoGeometry.Canonical.RicciMongeAmpere.IsSkewCurvatureTwoForm`
### Island 129 (1 decls)
  - `InfoGeometry.Krein.J_comp_K_of_relations`
### Island 130 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.periodic_flow_quantization_helper`
### Island 131 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_set_compact'`
### Island 132 (1 decls)
  - `InfoGeometry.Canonical.IB.pmf_normalize_apply_toReal`
### Island 133 (1 decls)
  - `InfoGeometry.Convex.radon_partition`
### Island 134 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.parity_time_commute`
### Island 135 (1 decls)
  - `InfoGeometry.Canonical.spineTagNames`
### Island 136 (1 decls)
  - `InfoGeometry.Architecture.SpinFactor.spinFactor_poly_identity`
### Island 137 (1 decls)
  - `InfoGeometry.Convex.helly_theorem_compact'`
### Island 138 (1 decls)
  - `InfoGeometry.Canonical.OpenProblemFormalization.parity_is_involution`
### Island 139 (1 decls)
  - `InfoGeometry.Meta.HiveLogos.unabstractedFVarNames`
### Island 140 (1 decls)
  - `InfoGeometry.Canonical.ManifoldDegree.exists_isolating_nhds_of_discrete`
### Island 141 (1 decls)
  - `InfoGeometry.Canonical.FUSION.Energy`
### Island 142 (1 decls)
  - `InfoGeometry.Canonical.HeadTrialityCore.splitDoubled128_dimension`
### Island 143 (1 decls)
  - `InfoGeometry.Projective.ConeBoundaryRaySpace`
### Island 144 (1 decls)
  - `InfoGeometry.Canonical.WeylEquivalence.weyl_denominator_is_euler_product`
### Island 145 (1 decls)
  - `InfoGeometry.LLM.PinCPTBridge.commutator`
### Island 146 (1 decls)
  - `InfoGeometry.Canonical.WeylEquivalence.PrimeGasEulerProduct`
### Island 147 (1 decls)
  - `InfoGeometry.Geometry.legendre_involution_of_inverse_maps`
### Island 148 (1 decls)
  - `InfoGeometry.Canonical.FUSION.FisherStiffness`
### Island 149 (1 decls)
  - `InfoGeometry.Jordan.logdet_square_nonneg_of_posDef`
