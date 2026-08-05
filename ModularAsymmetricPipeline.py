import numpy as np
from enum import IntEnum
from dataclasses import dataclass
from typing import Union

class PixelClass(IntEnum):
    BACKGROUND = 0
    COSMIC = 1
    DROPOUT = 2
    DOMAIN_FAULT = 3
    UNKNOWN_ANOMALY = 4

def stable_sigmoid(x):
    """Numerically stable sigmoid function."""
    x = np.asarray(x, dtype=np.float64)
    out = np.zeros_like(x)
    pos = x >= 0
    neg = ~pos
    out[pos] = 1.0 / (1.0 + np.exp(-x[pos]))
    out[neg] = np.exp(x[neg]) / (1.0 + np.exp(x[neg]))
    return out

class ModularAsymmetricCMOSPipeline:
    def __init__(self, a=1.0, b=0.0, domain_floor=1e-5, 
                 mu_admission=10.0, epsilon_admission=1.0, k_l_admission=0.5, admission_probability_cut=0.5,
                 tau_cosmic=25.0, epsilon_cosmic=2.0, k_l_cosmic=1.0, k_track=1.0, cosmic_probability_cut=0.5,
                 tau_dropout=15.0, epsilon_dropout=1.5, k_l_dropout=0.5, dropout_probability_cut=0.5):
        self.a = a
        self.b = b
        self.domain_floor = domain_floor
        
        self.mu_admission = mu_admission
        self.epsilon_admission = epsilon_admission
        self.k_l_admission = k_l_admission
        self.admission_probability_cut = admission_probability_cut
        
        self.tau_cosmic = tau_cosmic
        self.epsilon_cosmic = epsilon_cosmic
        self.k_l_cosmic = k_l_cosmic
        self.k_track = k_track
        self.cosmic_probability_cut = cosmic_probability_cut
        
        self.tau_dropout = tau_dropout
        self.epsilon_dropout = epsilon_dropout
        self.k_l_dropout = k_l_dropout
        self.dropout_probability_cut = dropout_probability_cut

    def process_frame(self, x, background, laplacian_score, track_support):
        x = np.asarray(x, dtype=np.float64)
        background = np.asarray(background, dtype=np.float64)
        laplacian_score = np.asarray(laplacian_score, dtype=np.float64)
        track_support = np.asarray(track_support, dtype=np.float64)
        
        arg_x = self.a * x + self.b
        arg_b = self.a * background + self.b

        valid_domain = (arg_x > self.domain_floor) & (arg_b > self.domain_floor)
        domain_fault = ~valid_domain

        deviance = np.zeros_like(x, dtype=np.float64)
        deviance[valid_domain] = (
            2.0 / (self.a * self.a) * (
                arg_x[valid_domain] * np.log(arg_x[valid_domain] / arg_b[valid_domain])
                - self.a * (x[valid_domain] - background[valid_domain])
            )
        )
        deviance = np.maximum(deviance, 0.0)

        positive_branch = valid_domain & (x > background)
        negative_branch = valid_domain & (x < background)

        d_positive = np.where(positive_branch, deviance, 0.0)
        d_negative = np.where(negative_branch, deviance, 0.0)

        l_positive = np.maximum(laplacian_score, 0.0)
        l_negative = np.maximum(-laplacian_score, 0.0)

        admission_energy = d_positive + d_negative + self.k_l_admission * laplacian_score**2
        cosmic_energy = d_positive + self.k_l_cosmic * l_positive**2 + self.k_track * track_support**2
        dropout_energy = d_negative + self.k_l_dropout * l_negative**2

        responsibility = np.where(
            valid_domain,
            stable_sigmoid((self.mu_admission - admission_energy) / self.epsilon_admission),
            0.0
        )
        
        cosmic_probability = np.where(
            positive_branch,
            stable_sigmoid((cosmic_energy - self.tau_cosmic) / self.epsilon_cosmic),
            0.0
        )
        cosmic_probability = np.where(domain_fault, 0.0, cosmic_probability)

        dropout_probability = np.where(
            negative_branch,
            stable_sigmoid((dropout_energy - self.tau_dropout) / self.epsilon_dropout),
            0.0
        )
        dropout_probability = np.where(domain_fault, 0.0, dropout_probability)

        state = np.full(x.shape, PixelClass.UNKNOWN_ANOMALY, dtype=np.uint8)
        state[domain_fault] = PixelClass.DOMAIN_FAULT

        cosmic_mask = valid_domain & positive_branch & (cosmic_probability >= self.cosmic_probability_cut)
        dropout_mask = valid_domain & negative_branch & (dropout_probability >= self.dropout_probability_cut)
        background_mask = valid_domain & ~cosmic_mask & ~dropout_mask & (responsibility >= self.admission_probability_cut)

        state[background_mask] = PixelClass.BACKGROUND
        state[cosmic_mask] = PixelClass.COSMIC
        state[dropout_mask] = PixelClass.DROPOUT

        return {
            'deviance': deviance,
            'd_positive': d_positive,
            'd_negative': d_negative,
            'responsibility': responsibility,
            'cosmic_prob': cosmic_probability,
            'dropout_prob': dropout_probability,
            'state': state
        }

if __name__ == "__main__":
    x = np.array([100.0, 1000.0, -10.0, 0.0, 50.0])
    bg = np.array([100.0, 100.0, 100.0, 100.0, 100.0])
    lap = np.array([0.0, 15.0, -5.0, -10.0, 1.0])
    trk = np.array([0.0, 1.0, 0.0, 0.0, 0.0])
    
    pipeline = ModularAsymmetricCMOSPipeline(
        a=1.0, b=10.0, domain_floor=0.01,
        mu_admission=5.0, epsilon_admission=1.0, admission_probability_cut=0.05,
        tau_cosmic=20.0, epsilon_cosmic=2.0, cosmic_probability_cut=0.5,
        tau_dropout=10.0, epsilon_dropout=1.5, dropout_probability_cut=0.5
    )
    
    res = pipeline.process_frame(x, bg, lap, trk)
    
    print("X:              ", x)
    print("Deviance:       ", res['deviance'])
    print("State:          ", res['state'])
    print("Admission R:    ", res['responsibility'])
    print("Cosmic Prob:    ", res['cosmic_prob'])
    print("Dropout Prob:   ", res['dropout_prob'])
