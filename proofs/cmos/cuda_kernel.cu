#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <cuda_runtime.h>

struct State {
    double mu;
    double N;
    double w_G;
    double w_P;
    double w_I;
    double C2;
    double C3;
    double C4;
    double C_G;
    double C_P;
    double C_I;
    bool is_initialized;
};

// CUDA Kernel
__global__ void cmos_estimator_kernel(const double* __restrict__ image_stack, 
                                      double* __restrict__ clean_image,
                                      bool* __restrict__ cr_mask,
                                      int width, int height, int num_frames,
                                      double c0, double c1, double c2,
                                      double pi_G, double pi_P, double pi_I,
                                      double T_beta, double rho, double rho_C,
                                      double c_t, double eps_t) {
    int x = blockIdx.x * blockDim.x + threadIdx.x;
    int y = blockIdx.y * blockDim.y + threadIdx.y;

    if (x >= width || y >= height) return;

    int pixel_idx = y * width + x;

    State state = {0.0, 0.0, pi_G, pi_P, pi_I, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, false};
    bool pixel_has_cr = false;

    for (int t = 0; t < num_frames; ++t) {
        int idx = t * (width * height) + pixel_idx;
        double val = image_stack[idx];

        if (!state.is_initialized) {
            state.mu = val;
            state.N = 0.0;
            state.is_initialized = true;
            continue;
        }

        // Divergences
        double z_G = 0.5 * (val - state.mu) * (val - state.mu) / c0;
        
        double z_P = 0.0;
        if (val > 0 && state.mu > 0) z_P = val * log(val / state.mu) - val + state.mu;
        else if (val == 0 && state.mu > 0) z_P = state.mu;

        double z_I = 1e9;
        if (val > 0 && state.mu > 0) z_I = val / state.mu - log(val / state.mu) - 1.0;

        double D_t = state.w_G * z_G + state.w_P * z_P + state.w_I * z_I;

        // Admission
        double r_t = 1.0 / (1.0 + exp(-(c_t - D_t) / eps_t));
        if (r_t < 0.5) {
            pixel_has_cr = true;
        }

        // Expert scores
        state.C_G = rho_C * state.C_G + r_t * z_G;
        state.C_P = rho_C * state.C_P + r_t * z_P;
        state.C_I = rho_C * state.C_I + r_t * z_I;

        // Softmax
        double logits_G = -state.C_G / T_beta + log(pi_G);
        double logits_P = -state.C_P / T_beta + log(pi_P);
        double logits_I = -state.C_I / T_beta + log(pi_I);

        double max_logits = fmax(logits_G, fmax(logits_P, logits_I));

        double exp_G = exp(logits_G - max_logits);
        double exp_P = exp(logits_P - max_logits);
        double exp_I = exp(logits_I - max_logits);

        double sum_exp = exp_G + exp_P + exp_I;
        state.w_G = exp_G / sum_exp;
        state.w_P = exp_P / sum_exp;
        state.w_I = exp_I / sum_exp;

        // Moments
        double W_a = rho * state.N;
        double C2_a = rho * state.C2;
        double C3_a = rho * state.C3;
        double C4_a = rho * state.C4;

        double W_prime = W_a + r_t;
        double delta = val - state.mu;

        if (W_prime > 0) {
            state.mu += (r_t / W_prime) * delta;
            state.C2 = C2_a + (delta * delta) * (W_a * r_t) / W_prime;
            state.C3 = C3_a + (pow(delta, 3)) * (W_a * r_t * (W_a - r_t)) / (W_prime * W_prime) -
                       3 * delta * (r_t * C2_a) / W_prime;
            state.C4 = C4_a + (pow(delta, 4)) * (W_a * r_t * (W_a * W_a - W_a * r_t + r_t * r_t)) / (pow(W_prime, 3)) +
                       6 * (delta * delta) * (r_t * r_t * C2_a) / (W_prime * W_prime) -
                       4 * delta * (r_t * C3_a) / W_prime;
        }

        state.N = W_prime;
    }

    clean_image[pixel_idx] = state.mu;
    cr_mask[pixel_idx] = pixel_has_cr;
}

int main() {
    int width = 10;
    int height = 10;
    int num_frames = 20;
    int num_pixels = width * height;

    std::vector<double> host_image_stack(num_frames * num_pixels, 100.0);
    
    // Inject CR at pixel (5, 5) frame 10
    int cr_x = 5, cr_y = 5, cr_t = 10;
    host_image_stack[cr_t * num_pixels + cr_y * width + cr_x] = 5000.0;

    double *d_image_stack, *d_clean_image;
    bool *d_cr_mask;

    cudaMalloc(&d_image_stack, num_frames * num_pixels * sizeof(double));
    cudaMalloc(&d_clean_image, num_pixels * sizeof(double));
    cudaMalloc(&d_cr_mask, num_pixels * sizeof(bool));

    cudaMemcpy(d_image_stack, host_image_stack.data(), num_frames * num_pixels * sizeof(double), cudaMemcpyHostToDevice);

    dim3 blockSize(16, 16);
    dim3 gridSize((width + blockSize.x - 1) / blockSize.x, (height + blockSize.y - 1) / blockSize.y);

    cmos_estimator_kernel<<<gridSize, blockSize>>>(d_image_stack, d_clean_image, d_cr_mask,
                                                   width, height, num_frames,
                                                   10.0, 0.5, 0.01,
                                                   0.333, 0.333, 0.334,
                                                   1.0, 0.99, 0.95,
                                                   20.0, 2.0);

    std::vector<double> host_clean_image(num_pixels);
    std::vector<bool> host_cr_mask(num_pixels);

    cudaMemcpy(host_clean_image.data(), d_clean_image, num_pixels * sizeof(double), cudaMemcpyDeviceToHost);
    cudaMemcpy(host_cr_mask.data(), d_cr_mask, num_pixels * sizeof(bool), cudaMemcpyDeviceToHost);

    std::cout << "CUDA Cosmic Ray Detection at (5, 5): " << (host_cr_mask[cr_y * width + cr_x] ? "YES" : "NO") << std::endl;
    std::cout << "CUDA Cosmic Ray Detection at (0, 0) (Baseline): " << (host_cr_mask[0] ? "YES" : "NO") << std::endl;

    cudaFree(d_image_stack);
    cudaFree(d_clean_image);
    cudaFree(d_cr_mask);

    return 0;
}
