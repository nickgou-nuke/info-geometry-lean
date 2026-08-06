#pragma once
#include <Eigen/Dense>
#include <cmath>
#include <complex>

using Complex = std::complex<double>;
using ConformalRotor = Eigen::Matrix4cd; // 4x4 Комплексна Матрица за SU(2,2)

class SU22Generators {
public:
    // 1. Лоренцов Бууст по оста Z (Модулярно Време / Rapidity)
    static ConformalRotor create_lorentz_boost_z(double t) {
        ConformalRotor B_t = ConformalRotor::Zero();
        double ch = std::cosh(t / 2.0);
        double sh = std::sinh(t / 2.0);
        
        // Диагонална репрезентация на Бууста: e^{(t/2) * γ_0 * γ_3}
        B_t(0, 0) = Complex(ch + sh, 0.0); // e^{t/2}
        B_t(1, 1) = Complex(ch - sh, 0.0); // e^{-t/2}
        B_t(2, 2) = Complex(ch - sh, 0.0); // e^{-t/2}
        B_t(3, 3) = Complex(ch + sh, 0.0); // e^{t/2}
        
        return B_t;
    }

    // 2. Туисторна Дилатация (Мащабиране на scale_inf)
    static ConformalRotor create_dilation(double lambda) {
        ConformalRotor D = ConformalRotor::Zero();
        double exp_pos = std::exp(lambda / 2.0);
        double exp_neg = std::exp(-lambda / 2.0);
        
        // Мащабира пространствената (ω) и импулсната (π) част обратнопропорционално
        D(0, 0) = Complex(exp_pos, 0.0);
        D(1, 1) = Complex(exp_pos, 0.0);
        D(2, 2) = Complex(exp_neg, 0.0);
        D(3, 3) = Complex(exp_neg, 0.0);
        
        return D;
    }
};
