#include <pybind11/pybind11.h>
#include <pybind11/numpy.h>
#include <stdexcept>

namespace py = pybind11;

extern "C" {
    void run_cl55_tensor_core(const void* h_A, const void* h_X, float* h_Y, int num_batches);
    void run_cl55_tensor_core_trace(const void* h_A, const void* h_X, float* h_trace_out, int num_batches);
    void* create_continuous_stream(int batches_per_frame);
    void destroy_continuous_stream(void* ptr);
    void stream_set_operator(void* ptr, const void* h_A);
    const float* stream_process_frame(void* ptr, const void* h_X);
}

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

py::array_t<float> apply_cl55_trace_projection(py::array_t<uint16_t> A, py::array_t<uint16_t> X) {
    py::buffer_info bufA = A.request();
    py::buffer_info bufX = X.request();

    if (bufA.ndim != 2 || bufA.shape[0] != 32 || bufA.shape[1] != 32) {
        throw std::runtime_error("Операторът A трябва да бъде матрица 32x32.");
    }

    if (bufX.ndim != 3 || bufX.shape[1] != 32 || bufX.shape[2] != 32) {
        throw std::runtime_error("Данните X трябва да бъдат тензор с размери (N, 32, 32).");
    }

    int num_batches = bufX.shape[0];

    py::array_t<float> Y({num_batches});
    py::buffer_info bufY = Y.request();

    run_cl55_tensor_core_trace(bufA.ptr, bufX.ptr, static_cast<float*>(bufY.ptr), num_batches);

    return Y;
}

class PyContinuousStream {
private:
    void* ptr;
    int batches_per_frame;
public:
    PyContinuousStream(int batches_per_frame_) : batches_per_frame(batches_per_frame_) {
        ptr = create_continuous_stream(batches_per_frame);
    }
    ~PyContinuousStream() {
        destroy_continuous_stream(ptr);
    }

    void set_operator(py::array_t<uint16_t> A) {
        py::buffer_info bufA = A.request();
        if (bufA.ndim != 2 || bufA.shape[0] != 32 || bufA.shape[1] != 32) {
            throw std::runtime_error("Операторът A трябва да бъде матрица 32x32.");
        }
        stream_set_operator(ptr, bufA.ptr);
    }

    py::array_t<float> process_frame_async(py::array_t<uint16_t> X) {
        py::buffer_info bufX = X.request();
        if (bufX.ndim != 3 || bufX.shape[0] != batches_per_frame || bufX.shape[1] != 32 || bufX.shape[2] != 32) {
            throw std::runtime_error("Данните X трябва да бъдат тензор с размери (batches_per_frame, 32, 32).");
        }
        
        const float* out_ptr = stream_process_frame(ptr, bufX.ptr);
        
        // Return a copy of the result. For true zero-copy we could use py::capsule but a 1D float array copy is extremely cheap.
        py::array_t<float> Y({batches_per_frame});
        std::memcpy(Y.mutable_data(), out_ptr, batches_per_frame * sizeof(float));
        return Y;
    }
};

PYBIND11_MODULE(cl55_cuda, m) {
    m.doc() = "Cℓ(5,5) Tensor Core Modular Flow Engine via PyBind11";
    m.def("apply_modular_flow", &apply_modular_flow, 
          "Изпълнява модулярния поток върху масиви от FITS данни, нативно в Tensor Cores.");
    m.def("apply_cl55_trace_projection", &apply_cl55_trace_projection,
          "Извлича макроскопичната интензивност (Gibbs-Fermi logit) директно на хардуерно ниво.");
          
    py::class_<PyContinuousStream>(m, "ContinuousStream")
        .def(py::init<int>())
        .def("set_operator", &PyContinuousStream::set_operator)
        .def("process_frame_async", &PyContinuousStream::process_frame_async);
}
