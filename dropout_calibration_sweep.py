import numpy as np
from ModularAsymmetricPipeline import ModularAsymmetricCMOSPipeline, PixelClass
from cross_validation_harness import TemporalFITSGenerator

def dropout_calibration_sweep():
    print("Initiating Stage C: Dropout-Specific Constrained Sweep...")
    
    gen = TemporalFITSGenerator(pedestal=200.0)
    B_star = gen.generate_latent_background()
    
    h_grid = [1, 2, 3, 5, 7, 10, 12, 14, 15, 20]
    local_sigma = np.sqrt(gen.c0 + gen.c1 * B_star[0, 0])
    
    best_loss = float('inf')
    best_params = {}
    
    for tau_drop in [10.0, 15.0, 25.0, 40.0]:
        for eps_drop in [1.5, 3.0, 5.0]:
            for k_l_drop in [0.0, 0.5]:
                
                pipeline = ModularAsymmetricCMOSPipeline(
                    a=1.0, b=0.0, domain_floor=1e-10,
                    mu_admission=18.76, epsilon_admission=3.23,
                    tau_cosmic=25.38, epsilon_cosmic=3.0,
                    tau_dropout=tau_drop, epsilon_dropout=eps_drop,
                    k_l_admission=0.0, k_l_cosmic=0.0, k_l_dropout=k_l_drop, k_track=0.0
                )
                
                recalls = []
                fpr_drop = 0
                diagnostics = []
                
                for h in h_grid:
                    X_clean = gen.generate_clean_frame(B_star)
                    truth = np.full(X_clean.shape, PixelClass.BACKGROUND)
                    
                    H_inj = h * local_sigma
                    X_inj = X_clean.copy()
                    mask = (np.random.rand(*X_clean.shape) < 0.05)
                    X_inj[mask] -= H_inj
                    truth[mask] = PixelClass.DROPOUT
                    
                    res = pipeline.process_frame(X_inj, B_star, np.zeros_like(X_clean), np.zeros_like(X_clean))
                    state = res['state']
                    
                    X_h_mean = 200.0 - H_inj
                    ax_plus_b = X_h_mean
                    
                    valid_domain_mask = (X_inj > 1e-10)
                    pr_valid = np.mean(valid_domain_mask[mask])
                    domain_fault_rate = np.mean(state[mask] == PixelClass.DOMAIN_FAULT)
                    
                    neg_branch = (X_inj < B_star) & valid_domain_mask
                    
                    true_drop = mask & neg_branch
                    pred_drop = (state == PixelClass.DROPOUT) & neg_branch
                    
                    tp = np.sum(true_drop & pred_drop)
                    fn = np.sum(true_drop & ~pred_drop)
                    fp = np.sum(~true_drop & pred_drop)
                    
                    recall_valid = tp / (tp + fn) if (tp + fn) > 0 else 0
                    recalls.append(recall_valid)
                    
                    overall_det = np.mean((state[mask] == PixelClass.DROPOUT) | (state[mask] == PixelClass.DOMAIN_FAULT))
                    
                    total_neg_valid = np.sum(neg_branch & ~mask)
                    fpr_current = fp / total_neg_valid if total_neg_valid > 0 else 0
                    if h == 5:
                        fpr_drop = fpr_current
                        
                    diagnostics.append((h, X_h_mean, ax_plus_b, pr_valid, recall_valid, domain_fault_rate, overall_det))
                
                avg_high_h_recall = np.mean(recalls[3:6]) # avg of h=5,7,10
                loss = -avg_high_h_recall + 1000 * max(0, fpr_drop - 0.0001)**2
                
                if loss < best_loss:
                    best_loss = loss
                    best_params = {
                        'tau_drop': tau_drop, 
                        'eps_drop': eps_drop, 
                        'k_l_drop': k_l_drop,
                        'diagnostics': diagnostics,
                        'fpr': fpr_drop
                    }
                    
    print("\n=== Optimal Dropout Configuration ===")
    print(f"tau_drop: {best_params['tau_drop']}")
    print(f"eps_drop: {best_params['eps_drop']}")
    print(f"k_l_drop: {best_params['k_l_drop']}")
    print(f"FPR_drop: {best_params['fpr']*1000000:.0f} per Megapixel")
    
    print("\n=== Detailed Final Diagnostic Sweep ===")
    print(f"{'h':>4} | {'X_h':>7} | {'aX+b':>7} | {'Pr(Valid)':>9} | {'Recall|Valid':>12} | {'DomainFault':>11} | {'OverallDet':>10}")
    print("-" * 75)
    for d in best_params['diagnostics']:
        print(f"{d[0]:4d} | {d[1]:7.1f} | {d[2]:7.1f} | {d[3]:9.3f} | {d[4]:12.3f} | {d[5]:11.3f} | {d[6]:10.3f}")

if __name__ == "__main__":
    dropout_calibration_sweep()
