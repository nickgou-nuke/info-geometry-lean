# GAP script for determining polygon orientation sign

PolygonOrientationSign := function(xA, yA, xB, yB, xC, yC)
    local determinant;
    
    # Using the expanded determinant formula:
    # det = (xB*yC + xA*yB + yA*xC) - (yA*xB + yB*xC + xA*yC)
    determinant := (xB*yC + xA*yB + yA*xC) - (yA*xB + yB*xC + xA*yC);
    
    if determinant > 0 then
        return "Counterclockwise";
    elif determinant < 0 then
        return "Clockwise";
    else
        return "Collinear";
    fi;
end;

# Example usage:
# Counterclockwise triangle
Print("Test 1 (CCW): ", PolygonOrientationSign(0, 0, 1, 0, 0, 1), "\n");

# Clockwise triangle
Print("Test 2 (CW): ", PolygonOrientationSign(0, 0, 0, 1, 1, 0), "\n");

# Collinear points
Print("Test 3 (Collinear): ", PolygonOrientationSign(0, 0, 1, 1, 2, 2), "\n");
