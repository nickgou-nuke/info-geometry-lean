#include <pybind11/pybind11.h>
#include <pybind11/numpy.h>
#include <stdexcept>

namespace py = pybind11;

// Външна декларация на CUDA функцията от Cl55TensorCore.cu
// type-pun към void* за да избегнем нуждата от включване на cuda_fp16.h тук
extern void run_cl55_tensor_core(const void* h_A, const void* h_X, float* h_Y, int num_batches);

/**
 * Експортиране към Python: 
 * Приема оператор A (32x32, float16) и batch от спинори X (N, 32, 32, float16).
 * Връща скаларен резултат Y (N, 32, 32, float32)
 */
py::array_t<float> apply_modular_flow(py::array_t<uint16_t> A, py::array_t<uint16_t> X) {
    py::buffer_info bufA = A.request();
    py::buffer_info bufX = X.request();

    // Защита и проверка на матричните размерности за Cℓ(5,5)
    if (bufA.ndim != 2 || bufA.shape[0] != 32 || bufA.shape[1] != 32) {
        throw std::runtime_error("Операторът A трябва да бъде матрица 32x32.");
    }

    if (bufX.ndim != 3 || bufX.shape[1] != 32 || bufX.shape[2] != 32) {
        throw std::runtime_error("Данните X трябва да бъдат тензор с размери (N, 32, 32).");
    }

    int num_batches = bufX.shape[0];

    // Алокиране на изходен numpy масив
    py::array_t<float> Y({num_batches, 32, 32});
    py::buffer_info bufY = Y.request();

    // Стартиране на Tensor Core двигателя
    run_cl55_tensor_core(bufA.ptr, bufX.ptr, static_cast<float*>(bufY.ptr), num_batches);

    return Y;
}

PYBIND11_MODULE(cl55_cuda, m) {
    m.doc() = "Cℓ(5,5) Tensor Core Modular Flow Engine via PyBind11";
    m.def("apply_modular_flow", &apply_modular_flow, 
          "Изпълнява модулярния поток върху масиви от FITS данни, нативно в Tensor Cores.");
}
