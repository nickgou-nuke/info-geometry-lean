import numpy as np
from ModularAsymmetricPipeline import ModularAsymmetricCMOSPipeline, PixelClass
from cross_validation_harness import TemporalFITSGenerator

def dropout_calibration_sweep():
    print("Initiating Stage C: Dropout-Specific Constrained Sweep...")
    
    gen = TemporalFITSGenerator(pedestal=200.0)
    B_star = gen.generate_latent_background()
    
    # Grid of dropout amplitudes (in noise units)
    h_grid = [1, 2, 3, 5, 7, 10, 15, 20]
    local_sigma = np.sqrt(gen.c0 + gen.c1 * B_star[0, 0])
    
    best_loss = float('inf')
    best_params = {}
    
    # Stage C grid for dropout parameters
    for tau_drop in [10.0, 15.0, 25.0, 40.0]:
        for eps_drop in [1.5, 3.0, 5.0]:
            for k_l_drop in [0.0, 0.5]:
                
                pipeline = ModularAsymmetricCMOSPipeline(
                    a=1.0, b=0.0, domain_floor=84.95,
                    mu_admission=18.76, epsilon_admission=3.23,
                    tau_cosmic=25.38, epsilon_cosmic=3.0,
                    tau_dropout=tau_drop, epsilon_dropout=eps_drop,
                    k_l_admission=0.0, k_l_cosmic=0.0, k_l_dropout=k_l_drop, k_track=0.0
                )
                
                recalls = []
                fp_count = 0
                total_neg_valid = 0
                
                for h in h_grid:
                    X = gen.generate_clean_frame(B_star)
                    truth = np.full(X.shape, PixelClass.BACKGROUND)
                    
                    # Inject dropout at h * sigma
                    mask = (np.random.rand(*X.shape) < 0.05)
                    X = gen.inject_dropout(X, H=(h * local_sigma), mask=mask)
                    truth[mask] = PixelClass.DROPOUT
                    
                    res = pipeline.process_frame(X, B_star, np.zeros_like(X), np.zeros_like(X))
                    state = res['state']
                    
                    # Evaluate only negative branch valid domain
                    neg_branch = (X < B_star) & (X > 84.95)
                    
                    true_drop = mask & neg_branch
                    pred_drop = (state == PixelClass.DROPOUT) & neg_branch
                    
                    tp = np.sum(true_drop & pred_drop)
                    fn = np.sum(true_drop & ~pred_drop)
                    fp = np.sum(~true_drop & pred_drop)
                    
                    recall = tp / (tp + fn) if (tp + fn) > 0 else 0
                    recalls.append(recall)
                    
                    fp_count += fp
                    total_neg_valid += np.sum(neg_branch & ~mask)
                
                fpr_drop = fp_count / total_neg_valid if total_neg_valid > 0 else 0
                
                # Custom loss for dropout: maximize recall at high h, penalize FPR
                # Only care about recall for h >= 5
                avg_high_h_recall = np.mean(recalls[3:])
                
                loss = -avg_high_h_recall + 1000 * max(0, fpr_drop - 0.001)**2
                
                if loss < best_loss:
                    best_loss = loss
                    best_params = {
                        'tau_drop': tau_drop, 
                        'eps_drop': eps_drop, 
                        'k_l_drop': k_l_drop,
                        'recalls': recalls,
                        'fpr': fpr_drop
                    }
                    
    print("\n=== Optimal Dropout Configuration ===")
    print(f"tau_drop: {best_params['tau_drop']}")
    print(f"eps_drop: {best_params['eps_drop']}")
    print(f"k_l_drop: {best_params['k_l_drop']}")
    print(f"FPR_drop: {best_params['fpr']:.5f}")
    
    print("\n=== Recall Curve ===")
    for h, r in zip(h_grid, best_params['recalls']):
        print(f"h = {h:2d} sigma: Recall = {r:.3f}")

if __name__ == "__main__":
    dropout_calibration_sweep()
