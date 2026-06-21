#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Kawamura's Infinite Wedge Representation & Recursive Fermion System
Based on "Extensions of representations of the CAR algebra to the Cuntz algebra O2"
"""

class MayaDiagram:
    """
    Represents a Maya Diagram M_+.
    A Maya diagram S is defined by its difference from the vacuum Z_{<= 0}.
    - particles: elements j > 0 that are IN S.
    - holes: elements j <= 0 that are NOT IN S.
    """
    def __init__(self, particles, holes):
        self.particles = frozenset(particles)
        self.holes = frozenset(holes)
        
    def __eq__(self, other):
        return self.particles == other.particles and self.holes == other.holes
    
    def __hash__(self):
        return hash((self.particles, self.holes))
        
    def d_plus(self):
        # d_+(S) = #(S ∩ Z_{+/2}) + #(Z_{-/2} \ S)
        # In our integer index:
        # S ∩ Z_{+/2} = particles
        # Z_{-/2} \ S = holes
        return len(self.particles) + len(self.holes)
    
    def display(self, window=5):
        s = "..."
        for j in range(-window, window + 1):
            if j > 0:
                s += "●" if j in self.particles else "○"
            else:
                s += "○" if j in self.holes else "●"
        s += "..."
        return s

class DualMayaDiagram:
    """
    Represents a Dual Maya Diagram M_-.
    Defined by difference from the dual vacuum Z_{>= 1}.
    - particles: elements j <= 0 that are IN S.
    - holes: elements j >= 1 that are NOT IN S.
    """
    def __init__(self, particles, holes):
        self.particles = frozenset(particles)
        self.holes = frozenset(holes)
        
    def __eq__(self, other):
        return self.particles == other.particles and self.holes == other.holes

    def __hash__(self):
        return hash((self.particles, self.holes))

    def d_minus_prime(self):
        # d'_-(S) = #(Z_{+/2} \ S) = holes
        return len(self.holes)
    
    def d_minus(self):
        # d_-(S) = #(Z_{+/2} \ S) + #(S ∩ Z_{-/2})
        return len(self.holes) + len(self.particles)
        
    def display(self, window=5):
        s = "..."
        for j in range(-window, window + 1):
            if j <= 0:
                s += "●" if j in self.particles else "○"
            else:
                s += "○" if j in self.holes else "●"
        s += "..."
        return s

# Vacuums
VACUUM = MayaDiagram(set(), set())
DUAL_VACUUM = DualMayaDiagram(set(), set())

def g1_maya(M: MayaDiagram):
    """ g1 on Maya returns DualMaya """
    # y >= 1 in g1(S) <=> 1-y not in M.holes
    new_holes = { y for y in range(1, max(M.holes, default=-1) * -1 + 3) if (1-y) in M.holes }
    # y <= 0 in g1(S) <=> -y in M.particles OR y == 0 (since 1 in argument is negated to 0)
    new_particles = { -p for p in M.particles }
    new_particles.add(0)
    return DualMayaDiagram(new_particles, new_holes)

def g2_maya(M: MayaDiagram):
    """ g2 on Maya returns DualMaya """
    new_holes = { y for y in range(1, max(M.holes, default=-1) * -1 + 3) if (1-y) in M.holes }
    new_particles = { -p for p in M.particles }
    return DualMayaDiagram(new_particles, new_holes)

def g1_dual(M: DualMayaDiagram):
    """ g1 on DualMaya returns Maya """
    # y > 0 in g1(S) <=> -y in M.particles OR y == 1
    new_particles = { -p for p in M.particles if p <= -1 }
    new_particles.add(1)
    # y <= 0 in g1(S) => hole if y not in g1(S). 
    new_holes = { y for y in range(0, min(M.holes, default=2) * -1 - 3, -1) if (1-y) in M.holes }
    return MayaDiagram(new_particles, new_holes)

def g2_dual(M: DualMayaDiagram):
    """ g2 on DualMaya returns Maya """
    new_particles = { -p for p in M.particles if p <= -1 }
    new_holes = { y for y in range(0, min(M.holes, default=2) * -1 - 3, -1) if (1-y) in M.holes }
    return MayaDiagram(new_particles, new_holes)

# We can define Cuntz operators on the basis vectors
class StateVector:
    def __init__(self, states):
        # states is a dict mapping (Diagram, IsDual) -> coefficient
        self.states = {k: v for k, v in states.items() if v != 0}
        
    def add(self, other):
        res = dict(self.states)
        for k, v in other.states.items():
            res[k] = res.get(k, 0) + v
        return StateVector(res)
        
    def scale(self, scalar):
        return StateVector({k: v * scalar for k, v in self.states.items()})

def S1_action(diagram, is_dual):
    if not is_dual:
        M = diagram
        sign = (-1)**M.d_plus()
        return StateVector({(g1_maya(M), True): sign})
    else:
        M = diagram
        sign = (-1)**M.d_minus_prime()
        return StateVector({(g1_dual(M), False): sign})

def S2_action(diagram, is_dual):
    if not is_dual:
        M = diagram
        sign = (-1)**M.d_plus()
        return StateVector({(g2_maya(M), True): sign})
    else:
        M = diagram
        sign = (-1)**M.d_minus()
        return StateVector({(g2_dual(M), False): sign})

def S1_star_action(diagram, is_dual):
    # The adjoint of an isometry mapped to permutation matrix is just the inverse function
    # For a given target D, we check if it is in the image of g1
    # Since this is a permutative representation, g1 and g2 partition the target space.
    if not is_dual:
        M = diagram
        # M is Maya. Was it from g1_dual?
        # g1_dual always has 1 in particles.
        if 1 in M.particles:
            # Reverse g1_dual
            old_particles = { -p for p in M.particles if p != 1 }
            old_holes = { 1-h for h in M.holes }
            src = DualMayaDiagram(old_particles, old_holes)
            sign = (-1)**src.d_minus_prime()
            return StateVector({(src, True): sign})
        return StateVector({})
    else:
        M = diagram
        # M is Dual. Was it from g1_maya?
        # g1_maya always has 0 in particles.
        if 0 in M.particles:
            old_particles = { -p for p in M.particles if p != 0 }
            old_holes = { 1-h for h in M.holes }
            src = MayaDiagram(old_particles, old_holes)
            sign = (-1)**src.d_plus()
            return StateVector({(src, False): sign})
        return StateVector({})

def S2_star_action(diagram, is_dual):
    if not is_dual:
        M = diagram
        # Was it from g2_dual?
        if 1 not in M.particles:
            old_particles = { -p for p in M.particles }
            old_holes = { 1-h for h in M.holes }
            src = DualMayaDiagram(old_particles, old_holes)
            sign = (-1)**src.d_minus()
            return StateVector({(src, True): sign})
        return StateVector({})
    else:
        M = diagram
        # Was it from g2_maya?
        if 0 not in M.particles:
            old_particles = { -p for p in M.particles }
            old_holes = { 1-h for h in M.holes }
            src = MayaDiagram(old_particles, old_holes)
            sign = (-1)**src.d_plus()
            return StateVector({(src, False): sign})
        return StateVector({})

def apply_op(vec: StateVector, op_func):
    res = StateVector({})
    for (diag, is_dual), coef in vec.states.items():
        res = res.add(op_func(diag, is_dual).scale(coef))
    return res

if __name__ == "__main__":
    print("Initializing Kawamura's Infinite Wedge Representation...")
    vac_vec = StateVector({(VACUUM, False): 1})
    
    print("Testing a_1 = s1 * s2* on vacuum:")
    res = apply_op(vac_vec, S2_star_action)
    res = apply_op(res, S1_action)
    
    for (d, is_dual), coef in res.states.items():
        print(f"Coef: {coef} | Diagram: {d.display()}")
