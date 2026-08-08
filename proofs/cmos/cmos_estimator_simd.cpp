#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <chrono>

class CmosEstimatorOracleSIMD {
private:
    double c0, c1, c2;
    double pi_G, pi_P, pi_I;
    double T_beta;
    double rho, rho_C;
    double c_t, eps_t;
    int num_pixels;

    // Struct of Arrays (SoA) for SIMD vectorization
    std::vector<double> mu;
    std::vector<double> N_state;
    std::vector<double> w_G;
    std::vector<double> w_P;
    std::vector<double> w_I;
    std::vector<double> C2;
    std::vector<double> C3;
    std::vector<double> C4;
    std::vector<double> C_G;
    std::vector<double> C_P;
    std::vector<double> C_I;
    std::vector<int> is_initialized;

public:
    CmosEstimatorOracleSIMD(int pixels, double c0, double c1, double c2,
                            double pi_G, double pi_P, double pi_I,
                            double T_beta, double rho, double rho_C,
                            double c_t, double eps_t)
        : num_pixels(pixels), c0(c0), c1(c1), c2(c2),
          pi_G(pi_G), pi_P(pi_P), pi_I(pi_I),
          T_beta(T_beta), rho(rho), rho_C(rho_C),
          c_t(c_t), eps_t(eps_t) {
        
        mu.assign(num_pixels, 0.0);
        N_state.assign(num_pixels, 0.0);
        w_G.assign(num_pixels, pi_G);
        w_P.assign(num_pixels, pi_P);
        w_I.assign(num_pixels, pi_I);
        C2.assign(num_pixels, 0.0);
        C3.assign(num_pixels, 0.0);
        C4.assign(num_pixels, 0.0);
        C_G.assign(num_pixels, 0.0);
        C_P.assign(num_pixels, 0.0);
        C_I.assign(num_pixels, 0.0);
        is_initialized.assign(num_pixels, 0);
    }

    // Process a full frame using OpenMP SIMD
    void update_frame(const double* x_in, bool* is_cr_out) {
        const double l_c0 = c0;
        const double l_c_t = c_t;
        const double l_eps_t = eps_t;
        const double l_rho_C = rho_C;
        const double l_rho = rho;
        const double l_T_beta = T_beta;
        const double log_pi_G = std::log(pi_G);
        const double log_pi_P = std::log(pi_P);
        const double log_pi_I = std::log(pi_I);

        double* p_mu = mu.data();
        double* p_N = N_state.data();
        double* p_w_G = w_G.data();
        double* p_w_P = w_P.data();
        double* p_w_I = w_I.data();
        double* p_C2 = C2.data();
        double* p_C3 = C3.data();
        double* p_C4 = C4.data();
        double* p_C_G = C_G.data();
        double* p_C_P = C_P.data();
        double* p_C_I = C_I.data();
        int* p_init = is_initialized.data();

        #pragma omp simd
        for (int i = 0; i < num_pixels; ++i) {
            double x = x_in[i];
            
            if (!p_init[i]) {
                p_mu[i] = x;
                p_N[i] = 0.0;
                p_init[i] = 1;
                is_cr_out[i] = false;
                continue;
            }

            double curr_mu = p_mu[i];

            // Bregman Divergences
            double z_G = 0.5 * (x - curr_mu) * (x - curr_mu) / l_c0;
            
            double z_P = 0.0;
            if (x > 0 && curr_mu > 0) z_P = x * std::log(x / curr_mu) - x + curr_mu;
            else if (x == 0 && curr_mu > 0) z_P = curr_mu;

            double z_I = 1e9;
            if (x > 0 && curr_mu > 0) z_I = x / curr_mu - std::log(x / curr_mu) - 1.0;

            // Combined energy
            double D_t = p_w_G[i] * z_G + p_w_P[i] * z_P + p_w_I[i] * z_I;

            // Admission responsibility
            double r_t = 1.0 / (1.0 + std::exp(-(l_c_t - D_t) / l_eps_t));
            is_cr_out[i] = (r_t < 0.5);

            // Expert scores
            double cg = l_rho_C * p_C_G[i] + r_t * z_G;
            double cp = l_rho_C * p_C_P[i] + r_t * z_P;
            double ci = l_rho_C * p_C_I[i] + r_t * z_I;
            
            p_C_G[i] = cg;
            p_C_P[i] = cp;
            p_C_I[i] = ci;

            // Softmax weights
            double logits_G = -cg / l_T_beta + log_pi_G;
            double logits_P = -cp / l_T_beta + log_pi_P;
            double logits_I = -ci / l_T_beta + log_pi_I;

            double max_logits = logits_G;
            if (logits_P > max_logits) max_logits = logits_P;
            if (logits_I > max_logits) max_logits = logits_I;

            double exp_G = std::exp(logits_G - max_logits);
            double exp_P = std::exp(logits_P - max_logits);
            double exp_I = std::exp(logits_I - max_logits);
            double sum_exp = exp_G + exp_P + exp_I;

            p_w_G[i] = exp_G / sum_exp;
            p_w_P[i] = exp_P / sum_exp;
            p_w_I[i] = exp_I / sum_exp;

            // Moments
            double W_a = l_rho * p_N[i];
            double W_prime = W_a + r_t;
            double delta = x - curr_mu;

            if (W_prime > 0) {
                double c2a = l_rho * p_C2[i];
                double c3a = l_rho * p_C3[i];
                double c4a = l_rho * p_C4[i];

                p_mu[i] += (r_t / W_prime) * delta;
                p_C2[i] = c2a + (delta * delta) * (W_a * r_t) / W_prime;
                p_C3[i] = c3a + (delta * delta * delta) * (W_a * r_t * (W_a - r_t)) / (W_prime * W_prime) -
                           3 * delta * (r_t * c2a) / W_prime;
                p_C4[i] = c4a + (delta * delta * delta * delta) * (W_a * r_t * (W_a * W_a - W_a * r_t + r_t * r_t)) / (W_prime * W_prime * W_prime) +
                           6 * (delta * delta) * (r_t * r_t * c2a) / (W_prime * W_prime) -
                           4 * delta * (r_t * c3a) / W_prime;
            }
            p_N[i] = W_prime;
        }
    }
};

int main() {
    const int num_pixels = 20000000; // 20 Megapixels
    const int num_frames = 10;
    
    CmosEstimatorOracleSIMD oracle(num_pixels, 10.0, 0.5, 0.01,
                                   0.333, 0.333, 0.334,
                                   1.0, 0.99, 0.95,
                                   20.0, 2.0);

    std::vector<double> frame(num_pixels, 100.0);
    std::vector<bool> cr_mask_temp; // Just a placeholder, we use char array for data
    std::vector<char> cr_mask(num_pixels, 0);

    // Warm-up
    oracle.update_frame(frame.data(), (bool*)cr_mask.data());

    std::cout << "Benchmarking 20-Megapixel CMOS stream over " << num_frames << " frames..." << std::endl;
    auto start_time = std::chrono::high_resolution_clock::now();

    bool detected = false;
    for (int t = 0; t < num_frames; ++t) {
        // Inject a synthetic cosmic ray in the middle of the frame
        if (t == 5) frame[num_pixels / 2] = 5000.0;
        
        oracle.update_frame(frame.data(), (bool*)cr_mask.data());
        
        if (t == 5 && cr_mask[num_pixels / 2]) {
            detected = true;
        }
        
        // Reset the cosmic ray after injection
        if (t == 5) frame[num_pixels / 2] = 100.0;
    }

    auto end_time = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end_time - start_time;

    double fps = num_frames / diff.count();
    std::cout << "Total Time: " << diff.count() << " seconds" << std::endl;
    std::cout << "Throughput: " << fps << " FPS" << std::endl;
    
    // Check detection
    if (detected) {
        std::cout << "Cosmic ray successfully detected at index " << num_pixels / 2 << std::endl;
    } else {
        std::cout << "Failed to detect cosmic ray!" << std::endl;
    }

    return 0;
}
