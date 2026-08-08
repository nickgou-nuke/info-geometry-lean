# Extremal Vertex Sort
# Formulates the lexicographic ordering of vertices to mathematically select the convex hull extremal vertex

ExtremalVertexSort := function(vertices)
    Sort(vertices, function(u, v)
        # Sort by min X, then by min Y
        if u[1] < v[1] then
            return true;
        elif u[1] = v[1] and u[2] < v[2] then
            return true;
        else
            return false;
        fi;
    end);
    return vertices;
end;

# Example usage
vertices := [[3, 2], [1, 5], [1, 2], [4, 1]];
Print("Original vertices: ", vertices, "\n");
ExtremalVertexSort(vertices);
Print("Sorted vertices (Lexicographic, Extremal First): ", vertices, "\n");
