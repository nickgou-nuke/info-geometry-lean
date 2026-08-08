import sympy
from galgebra.ga import Ga
from galgebra.mv import Mv

def main():
    # Setup coordinates and geometric algebra for 2D space
    coords = sympy.symbols('x y', real=True)
    ga = Ga('e_x e_y', g=[1, 1], coords=coords)
    ex, ey = ga.mv()
    
    # Define a parameter t
    t = sympy.symbols('t', real=True)
    
    # Define a parameterized curve, e.g., a parabola y = x^2
    # c(t) = t * e_x + t^2 * e_y
    c = t * ex + (t**2) * ey
    print("Parameterized curve c(t):")
    print(c)
    
    # Calculate the tangent vector by differentiating with respect to t
    # For galgebra, Mv elements can be differentiated with respect to scalar parameters.
    dc_dt = c.diff(t)
    print("\nTangent vector dc/dt:")
    print(dc_dt)
    
    # Now reverse the parameterization: let u = -t, so t = -u
    u = sympy.symbols('u', real=True)
    c_rev = c.subs({t: -u})
    print("\nReversed parameterized curve c(-u):")
    print(c_rev)
    
    # Calculate the tangent vector of the reversed curve with respect to u
    dc_rev_du = c_rev.diff(u)
    print("\nTangent vector of reversed curve d(c(-u))/du:")
    print(dc_rev_du)
    
    # Verify the relationship between the tangents
    t0 = sympy.symbols('t0', real=True)
    tangent_t0 = dc_dt.subs({t: t0})
    tangent_rev_minus_t0 = dc_rev_du.subs({u: -t0})
    
    print("\nTangent at t=t0:")
    print(tangent_t0)
    print("\nTangent of reversed curve at u=-t0:")
    print(tangent_rev_minus_t0)
    
    # Check if they are negations of each other
    is_negated = (tangent_t0 == -tangent_rev_minus_t0)
    print(f"\nIs the tangent negated when parameterization is reversed? {is_negated}")

if __name__ == '__main__':
    main()
