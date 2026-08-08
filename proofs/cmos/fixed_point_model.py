import math
import numpy as np

class FixedPointEstimator:
    """
    Bit-accurate fixed-point model for the Three-Expert Bregman Estimator.
    We simulate Q16.16 fixed-point arithmetic.
    """
    def __init__(self, c0_f, c1_f, c2_f, pi_G_f, pi_P_f, pi_I_f, T_beta_f, rho_f, rho_C_f, c_t_f, eps_t_f):
        self.SHIFT = 16
        self.ONE = 1 << self.SHIFT
        
        self.c0 = self.to_fp(c0_f)
        self.c1 = self.to_fp(c1_f)
        self.c2 = self.to_fp(c2_f)
        
        self.pi_G = self.to_fp(pi_G_f)
        self.pi_P = self.to_fp(pi_P_f)
        self.pi_I = self.to_fp(pi_I_f)
        
        self.T_beta = self.to_fp(T_beta_f)
        self.rho = self.to_fp(rho_f)
        self.rho_C = self.to_fp(rho_C_f)
        
        self.c_t = self.to_fp(c_t_f)
        self.eps_t = self.to_fp(eps_t_f)
        
        # State
        self.is_initialized = False
        self.mu = 0
        self.N = 0
        self.C_G = 0
        self.C_P = 0
        self.C_I = 0
        self.w_G = self.pi_G
        self.w_P = self.pi_P
        self.w_I = self.pi_I

    def to_fp(self, val: float) -> int:
        return int(val * self.ONE)

    def to_float(self, val: int) -> float:
        return val / self.ONE
        
    def mul_fp(self, a: int, b: int) -> int:
        return (a * b) >> self.SHIFT

    def div_fp(self, a: int, b: int) -> int:
        if b == 0: return 0
        return (a << self.SHIFT) // b

    def log_fp(self, a: int) -> int:
        # Simple lookup / math proxy for log in fixed point
        if a <= 0: return 0
        return self.to_fp(math.log(self.to_float(a)))

    def exp_fp(self, a: int) -> int:
        val = self.to_float(a)
        if val > 50.0: val = 50.0
        if val < -50.0: val = -50.0
        return self.to_fp(math.exp(val))

    def d_G(self, x: int, mu: int) -> int:
        d = x - mu
        d_sq = self.mul_fp(d, d)
        d_sq_half = d_sq >> 1
        return self.div_fp(d_sq_half, self.c0)

    def d_P(self, x: int, mu: int) -> int:
        if x > 0 and mu > 0:
            ratio = self.div_fp(x, mu)
            l = self.log_fp(ratio)
            term1 = self.mul_fp(x, l)
            return term1 - x + mu
        elif x == 0 and mu > 0:
            return mu
        return 0

    def d_I(self, x: int, mu: int) -> int:
        if x > 0 and mu > 0:
            ratio = self.div_fp(x, mu)
            l = self.log_fp(ratio)
            return ratio - l - self.ONE
        return self.to_fp(1e9)

    def update(self, x_f: float, is_clipped: bool = False):
        x = self.to_fp(x_f)
        
        if not self.is_initialized:
            self.mu = x
            self.N = 0
            self.is_initialized = True
            return self.to_float(self.mu), False

        z_G = self.d_G(x, self.mu)
        z_P = self.d_P(x, self.mu)
        z_I = self.d_I(x, self.mu)

        term_G = self.mul_fp(self.w_G, z_G)
        term_P = self.mul_fp(self.w_P, z_P)
        term_I = self.mul_fp(self.w_I, z_I)
        
        D_t = term_G + term_P + term_I

        r_t = 0
        if not is_clipped:
            diff = self.c_t - D_t
            div = self.div_fp(diff, self.eps_t)
            exp_val = self.exp_fp(-div)
            r_t = self.div_fp(self.ONE, self.ONE + exp_val)

        is_cr = r_t < (self.ONE >> 1) # r_t < 0.5

        # Update expert scores
        self.C_G = self.mul_fp(self.rho_C, self.C_G) + self.mul_fp(r_t, z_G)
        self.C_P = self.mul_fp(self.rho_C, self.C_P) + self.mul_fp(r_t, z_P)
        self.C_I = self.mul_fp(self.rho_C, self.C_I) + self.mul_fp(r_t, z_I)

        W_a = self.mul_fp(self.rho, self.N)
        W_prime = W_a + r_t
        delta = x - self.mu

        if W_prime > 0:
            ratio = self.div_fp(r_t, W_prime)
            shift_val = self.mul_fp(ratio, delta)
            self.mu += shift_val

        self.N = W_prime
        
        return self.to_float(self.mu), is_cr

if __name__ == "__main__":
    fp_oracle = FixedPointEstimator(c0_f=10.0, c1_f=0.5, c2_f=0.01,
                                    pi_G_f=0.333, pi_P_f=0.333, pi_I_f=0.334,
                                    T_beta_f=1.0, rho_f=0.99, rho_C_f=0.95,
                                    c_t_f=20.0, eps_t_f=2.0)

    sequence = [
        105.0, 95.0, 102.0, 98.0, 103.0,
        96.0, 101.0, 99.0, 104.0, 97.0,
        5000.0, # Cosmic ray
        100.0, 98.0, 102.0, 99.0,
        101.0, 97.0, 103.0, 98.0, 100.0
    ]

    for t, val in enumerate(sequence):
        mu_f, is_cr = fp_oracle.update(val)
        print(f"t={t:2d} x={val:6.1f} -> mu_fixed={mu_f:7.3f} | CR={'YES' if is_cr else 'NO'}")
