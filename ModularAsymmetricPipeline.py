import numpy as np

def stable_sigmoid(x):
    """Numerically stable sigmoid function."""
    x = np.asarray(x)
    out = np.zeros_like(x)
    
    pos = x >= 0
    neg = ~pos
    
    out[pos] = 1.0 / (1.0 + np.exp(-x[pos]))
    out[neg] = np.exp(x[neg]) / (1.0 + np.exp(x[neg]))
    return out

class ModularAsymmetricCMOSPipeline:
    def __init__(self, a=1.0, b=0.0, domain_floor=1e-5, 
                 mu_admission=10.0, epsilon_admission=1.0, k_l_admission=0.5,
                 tau_cosmic=25.0, epsilon_cosmic=2.0, k_l_cosmic=1.0, k_track=1.0,
                 tau_dropout=15.0, epsilon_dropout=1.5, k_l_dropout=0.5,
                 responsibility_cut=0.05):
        # Scale/Shift parameters for deviance domain mapping (e.g. analog-to-digital conversion factors)
        self.a = a
        self.b = b
        self.domain_floor = domain_floor
        
        # Admission hyperparameters
        self.mu_admission = mu_admission
        self.epsilon_admission = epsilon_admission
        self.k_l_admission = k_l_admission
        
        # Cosmic Ray hyperparameters
        self.tau_cosmic = tau_cosmic
        self.epsilon_cosmic = epsilon_cosmic
        self.k_l_cosmic = k_l_cosmic
        self.k_track = k_track
        
        # Dropout hyperparameters
        self.tau_dropout = tau_dropout
        self.epsilon_dropout = epsilon_dropout
        self.k_l_dropout = k_l_dropout
        
        # Sigmoid probability cut
        self.responsibility_cut = responsibility_cut

    def process_frame(self, x, background, laplacian_score, track_support):
        """
        Process a FITS frame natively tracking positive CRs, negative dropouts, 
        background admission, and domain failures without unsafe numerical clipping.
        """
        # Ensure arrays
        x = np.asarray(x, dtype=np.float64)
        background = np.asarray(background, dtype=np.float64)
        laplacian_score = np.asarray(laplacian_score, dtype=np.float64)
        track_support = np.asarray(track_support, dtype=np.float64)
        
        # 1. Precise domain tracking
        arg_x = self.a * x + self.b
        arg_b = self.a * background + self.b

        valid_domain = (arg_x > self.domain_floor) & (arg_b > self.domain_floor)
        domain_fault = ~valid_domain

        # 2. Raw unclipped deviance computation on valid domain
        deviance = np.zeros_like(x, dtype=np.float64)
        
        deviance[valid_domain] = (
            2.0 / (self.a * self.a)
            * (
                arg_x[valid_domain]
                * np.log(
                    arg_x[valid_domain] / arg_b[valid_domain]
                )
                - self.a * (
                    x[valid_domain] - background[valid_domain]
                )
            )
        )
        # Fix extremely tiny negative values due to floating point error near minimum
        deviance = np.maximum(deviance, 0.0)

        # 3. Particle-hole branch splitting (D_+ and D_-)
        positive_branch = valid_domain & (x >= background)
        negative_branch = valid_domain & (x < background)

        d_positive = np.where(positive_branch, deviance, 0.0)
        d_negative = np.where(negative_branch, deviance, 0.0)

        l_positive = np.maximum(laplacian_score, 0.0)
        l_negative = np.maximum(-laplacian_score, 0.0)

        # 4. Energy thresholds
        admission_energy = (
            d_positive + d_negative + self.k_l_admission * laplacian_score**2
        )

        cosmic_energy = (
            d_positive + self.k_l_cosmic * l_positive**2 + self.k_track * track_support**2
        )

        dropout_energy = (
            d_negative + self.k_l_dropout * l_negative**2
        )

        # 5. Sigmoid probability mappings
        responsibility = stable_sigmoid(
            (self.mu_admission - admission_energy) / self.epsilon_admission
        )

        cosmic_probability = stable_sigmoid(
            (cosmic_energy - self.tau_cosmic) / self.epsilon_cosmic
        )

        dropout_probability = stable_sigmoid(
            (dropout_energy - self.tau_dropout) / self.epsilon_dropout
        )

        # 6. Apply Domain Fault masking (Domain Fault -> R=0)
        responsibility = np.where(valid_domain, responsibility, 0.0)

        # 7. Final Hard-cut sparsity filter
        responsibility = np.where(
            responsibility >= self.responsibility_cut,
            responsibility,
            0.0
        )
        
        # Classification assignment
        return {
            'deviance': deviance,
            'admission_energy': admission_energy,
            'cosmic_energy': cosmic_energy,
            'dropout_energy': dropout_energy,
            'responsibility': responsibility,
            'cosmic_prob': cosmic_probability,
            'dropout_prob': dropout_probability,
            'valid_domain': valid_domain,
            'domain_fault': domain_fault,
            'd_positive': d_positive,
            'd_negative': d_negative
        }

if __name__ == "__main__":
    # Small test on synthetic pixels
    x = np.array([100.0, 1000.0, -10.0, 0.0, 50.0]) # Nominal, CR, Domain Fault, Dropout, Minor noise
    bg = np.array([100.0, 100.0, 100.0, 100.0, 100.0])
    lap = np.array([0.0, 15.0, -5.0, -10.0, 1.0])
    trk = np.array([0.0, 1.0, 0.0, 0.0, 0.0])
    
    pipeline = ModularAsymmetricCMOSPipeline(
        a=1.0, b=10.0, domain_floor=0.01,
        mu_admission=5.0, epsilon_admission=1.0,
        tau_cosmic=20.0, epsilon_cosmic=2.0,
        tau_dropout=10.0, epsilon_dropout=1.5
    )
    
    res = pipeline.process_frame(x, bg, lap, trk)
    
    print("X:              ", x)
    print("Deviance:       ", res['deviance'])
    print("Domain Fault:   ", res['domain_fault'])
    print("Admission R:    ", res['responsibility'])
    print("Cosmic Prob:    ", res['cosmic_prob'])
    print("Dropout Prob:   ", res['dropout_prob'])
