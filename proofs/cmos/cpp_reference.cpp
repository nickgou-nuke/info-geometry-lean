#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <iomanip>

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

class CmosEstimatorOracle {
private:
    double c0, c1, c2;
    double pi_G, pi_P, pi_I;
    double T_beta;
    double rho, rho_C;
    double c_t, eps_t;
    State state;

public:
    CmosEstimatorOracle(double c0, double c1, double c2,
                        double pi_G, double pi_P, double pi_I,
                        double T_beta, double rho, double rho_C,
                        double c_t, double eps_t)
        : c0(c0), c1(c1), c2(c2),
          pi_G(pi_G), pi_P(pi_P), pi_I(pi_I),
          T_beta(T_beta), rho(rho), rho_C(rho_C),
          c_t(c_t), eps_t(eps_t) {
        state = {0.0, 0.0, pi_G, pi_P, pi_I, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, false};
    }

    double variance(double u) const {
        return c0 + c1 * u + c2 * u * u;
    }

    double d_G(double x, double mu) const {
        return 0.5 * (x - mu) * (x - mu) / c0;
    }

    double d_P(double x, double mu) const {
        if (x > 0 && mu > 0) {
            return x * std::log(x / mu) - x + mu;
        } else if (x == 0 && mu > 0) {
            return mu;
        }
        return 0.0;
    }

    double d_I(double x, double mu) const {
        if (x > 0 && mu > 0) {
            return x / mu - std::log(x / mu) - 1.0;
        }
        return 1e9; // handle invalid domain
    }

    // Returns a pair of (mu, is_cosmic_ray)
    std::pair<double, bool> update(double x, bool is_clipped = false) {
        if (!state.is_initialized) {
            state.mu = x;
            state.N = 0.0;
            state.is_initialized = true;
            return {state.mu, false};
        }

        double z_G = d_G(x, state.mu);
        double z_P = d_P(x, state.mu);
        double z_I = d_I(x, state.mu);

        double D_t = state.w_G * z_G + state.w_P * z_P + state.w_I * z_I;

        double r_t = 0.0;
        if (!is_clipped) {
            r_t = 1.0 / (1.0 + std::exp(-(c_t - D_t) / eps_t));
        }

        bool is_cosmic_ray = r_t < 0.5;

        state.C_G = rho_C * state.C_G + r_t * z_G;
        state.C_P = rho_C * state.C_P + r_t * z_P;
        state.C_I = rho_C * state.C_I + r_t * z_I;

        double logits_G = -state.C_G / T_beta + std::log(pi_G);
        double logits_P = -state.C_P / T_beta + std::log(pi_P);
        double logits_I = -state.C_I / T_beta + std::log(pi_I);

        double max_logits = std::max({logits_G, logits_P, logits_I});

        double exp_G = std::exp(logits_G - max_logits);
        double exp_P = std::exp(logits_P - max_logits);
        double exp_I = std::exp(logits_I - max_logits);

        double sum_exp = exp_G + exp_P + exp_I;
        state.w_G = exp_G / sum_exp;
        state.w_P = exp_P / sum_exp;
        state.w_I = exp_I / sum_exp;

        double W_a = rho * state.N;
        double C2_a = rho * state.C2;
        double C3_a = rho * state.C3;
        double C4_a = rho * state.C4;

        double W_prime = W_a + r_t;
        double delta = x - state.mu;

        if (W_prime > 0) {
            state.mu += (r_t / W_prime) * delta;

            state.C2 = C2_a + (delta * delta) * (W_a * r_t) / W_prime;

            state.C3 = C3_a + (std::pow(delta, 3)) * (W_a * r_t * (W_a - r_t)) / (W_prime * W_prime) -
                       3 * delta * (r_t * C2_a) / W_prime;

            state.C4 = C4_a + (std::pow(delta, 4)) * (W_a * r_t * (W_a * W_a - W_a * r_t + r_t * r_t)) / (std::pow(W_prime, 3)) +
                       6 * (delta * delta) * (r_t * r_t * C2_a) / (W_prime * W_prime) -
                       4 * delta * (r_t * C3_a) / W_prime;
        }

        state.N = W_prime;

        return {state.mu, is_cosmic_ray};
    }
};

int main() {
    CmosEstimatorOracle oracle(10.0, 0.5, 0.01,
                               0.333, 0.333, 0.334,
                               1.0, 0.99, 0.95,
                               20.0, 2.0);

    // Simulate 20 frames for one pixel
    std::vector<double> sequence = {
        105.0, 95.0, 102.0, 98.0, 103.0,
        96.0, 101.0, 99.0, 104.0, 97.0,
        5000.0, // Cosmic ray
        100.0, 98.0, 102.0, 99.0,
        101.0, 97.0, 103.0, 98.0, 100.0
    };

    for (size_t t = 0; t < sequence.size(); ++t) {
        auto [mu, is_cr] = oracle.update(sequence[t]);
        std::cout << "t=" << std::setw(2) << t 
                  << " x=" << std::setw(6) << sequence[t] 
                  << " -> mu=" << std::setw(8) << std::fixed << std::setprecision(3) << mu 
                  << " | CR=" << (is_cr ? "YES" : "NO") << std::endl;
    }

    return 0;
}
