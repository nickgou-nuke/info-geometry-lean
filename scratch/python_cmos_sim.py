import numpy as np
from scipy.ndimage import convolve
from enum import IntEnum

class PixelClass(IntEnum):
    BACKGROUND = 0
    COSMIC = 1
    DROPOUT = 2
    DOMAIN_FAULT = 3
    UNKNOWN_ANOMALY = 4

class ModularMoebiusCMOSPipeline:
    def __init__(self, shape, params):
        self.params = params
        self.shape = shape
        
        # Canonical barycenter B and statistical memory N
        self.B = np.zeros(shape, dtype=np.float32)
        self.N = np.ones(shape, dtype=np.float32) * 10.0
        self.is_initialized = False
        
        # Calibrated Laplacian for spatial coherence
        self.laplacian_kernel = np.array([
            [ 0, -1,  0],
            [-1,  4, -1],
            [ 0, -1,  0]
        ], dtype=np.float32)

    def process_frame(self, X_adu):
        """
        Uses the exact modular relation to rectify the Möbius flow.
        Returns the updated background, the strict PixelClass states, and the probabilities.
        """
        if not self.is_initialized:
            self.B = np.clip(self.params['gain'] * (X_adu - self.params['pedestal']), 0.0, None)
            self.is_initialized = True
            return self.B, np.full(self.shape, PixelClass.BACKGROUND, dtype=np.uint8), {}

        # 1. Electron domain
        X_e = self.params['gain'] * (X_adu - self.params['pedestal'])
        noise_floor = max(self.params['read_noise_e_sq'] + self.params['quantization_noise_e_sq'], self.params['variance_floor'])

        # Check for domain faults
        log_argument_floor = self.params.get('log_argument_floor', 1e-10)
        hardware_cut = self.params.get('hardware_low_signal_cut', -1e9)
        
        arg_X = X_e + noise_floor
        arg_B = self.B + noise_floor
        
        math_valid = (arg_X > log_argument_floor) & (arg_B > log_argument_floor)
        hw_valid = (X_e >= hardware_cut)
        
        valid_domain = math_valid & hw_valid
        domain_fault = ~valid_domain

        # 2. Fisher amplitude via exact quasi-deviance
        deviance = np.zeros_like(X_e, dtype=np.float64)
        
        deviance[valid_domain] = 2.0 * (
            arg_X[valid_domain] * np.log(arg_X[valid_domain] / arg_B[valid_domain]) 
            - (X_e[valid_domain] - self.B[valid_domain])
        )
        deviance = np.maximum(deviance, 0.0)
        
        # Branch splitting strictly on valid domain
        positive_branch = valid_domain & (X_e >= self.B)
        negative_branch = valid_domain & (X_e < self.B)

        d_positive = np.where(positive_branch, deviance, 0.0)
        d_negative = np.where(negative_branch, deviance, 0.0)

        # 3. Spatial Laplacian (Whitening)
        # Prevent div by zero or sqrt of negative in invalid domain
        safe_arg_B = np.where(valid_domain, arg_B, 1.0)
        laplacian_score = convolve(X_e, self.laplacian_kernel, mode='mirror') / np.sqrt(safe_arg_B)
        laplacian_score = np.where(valid_domain, laplacian_score, 0.0)
        
        l_positive = np.maximum(laplacian_score, 0.0)
        l_negative = np.maximum(-laplacian_score, 0.0)

        # 4. Asymmetric Energies
        admission_energy = (
            d_positive 
            + d_negative 
            + self.params.get('k_l_admission', 0.0) * laplacian_score**2
        )
        
        cosmic_energy = (
            d_positive 
            + self.params.get('k_l_cosmic', self.params.get('k_L', 0.0)) * l_positive**2
        )
        
        dropout_energy = (
            d_negative 
            + self.params.get('k_l_dropout', 0.0) * l_negative**2
        )

        # 5. Classifications
        def stable_sigmoid(x):
            return 1.0 / (1.0 + np.exp(-x))

        responsibility = stable_sigmoid(
            (self.params.get('mu_admission', self.params.get('mu_c', 0.0)) - admission_energy) 
            / self.params.get('epsilon_admission', self.params.get('epsilon', 1.0))
        )
        
        # Branch gating of probability heads
        cosmic_probability = np.where(
            positive_branch,
            stable_sigmoid(
                (cosmic_energy - self.params.get('tau_cosmic', self.params.get('cosmic_threshold', 0.0)))
                / self.params.get('epsilon_cosmic', self.params.get('epsilon', 1.0))
            ),
            0.0
        )
        
        dropout_probability = np.where(
            negative_branch,
            stable_sigmoid(
                (dropout_energy - self.params.get('tau_dropout', 1e9))
                / self.params.get('epsilon_dropout', self.params.get('epsilon', 1.0))
            ),
            0.0
        )

        # Mask probabilities strictly where domain fails
        responsibility = np.where(domain_fault, 0.0, responsibility)
        cosmic_probability = np.where(domain_fault, 0.0, cosmic_probability)
        dropout_probability = np.where(domain_fault, 0.0, dropout_probability)
        
        # Hard thresholding for discrete states
        admission_cut = self.params.get('responsibility_cut', 0.01)
        cosmic_cut = self.params.get('cosmic_probability_cut', 0.5)
        dropout_cut = self.params.get('dropout_probability_cut', 0.5)
        
        responsibility = np.where(responsibility >= admission_cut, responsibility, 0.0)

        # State assignment logic
        state = np.full(self.shape, PixelClass.UNKNOWN_ANOMALY, dtype=np.uint8)
        state[domain_fault] = PixelClass.DOMAIN_FAULT

        cosmic_mask = valid_domain & positive_branch & (cosmic_probability >= cosmic_cut)
        dropout_mask = valid_domain & negative_branch & (dropout_probability >= dropout_cut)
        
        background_mask = valid_domain & ~cosmic_mask & ~dropout_mask & (responsibility >= admission_cut)

        state[background_mask] = PixelClass.BACKGROUND
        state[cosmic_mask] = PixelClass.COSMIC
        state[dropout_mask] = PixelClass.DROPOUT

        # 6. Protected recursive Jaynes barycenter
        valid_gate = responsibility > 0.0
        omega_t = np.zeros(self.shape, dtype=np.float32)
        
        rho = self.params.get('rho', 0.99)
        omega_t[valid_gate] = responsibility[valid_gate] / (rho * self.N[valid_gate] + responsibility[valid_gate])

        self.B += omega_t * (X_e - self.B)
        self.B = np.clip(self.B, 0.0, None)
        self.N = rho * self.N + responsibility

        return self.B, state, {'r': responsibility, 'p_CR': cosmic_probability, 'p_drop': dropout_probability}
