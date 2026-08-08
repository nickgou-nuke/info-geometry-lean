#include <pybind11/pybind11.h>
#include <pybind11/numpy.h>
#include <cuda_fp16.h>

namespace py = pybind11;

// Forward declarations of the CUDA launcher functions
void run_cl55_tensor_core(const half* h_A, const half* h_X, float* h_Y, int num_batches);
void run_cl55_tensor_core_trace(const half* h_A, const half* h_X, float* h_trace_out, int num_batches);

class ContinuousCl55Stream {
public:
    ContinuousCl55Stream(int _batches_per_frame);
    ~ContinuousCl55Stream();
    void set_operator(const half* A_src);
    const float* process_frame_async(const half* frame_data);
};

// Helper function to convert numpy float16 to cuda half
void convert_fp16_to_half(const py::array_t<uint16_t>& np_array, half* cu_array, size_t size) {
    const uint16_t* ptr = np_array.data();
    for (size_t i = 0; i < size; ++i) {
        cu_array[i] = __ushort_as_half(ptr[i]);
    }
}

// Full Tensor Flow
py::array_t<float> apply_cl55_tensor_flow(py::array_t<uint16_t> A, py::array_t<uint16_t> X) {
    py::buffer_info buf_A = A.request();
    py::buffer_info buf_X = X.request();
    
    if (buf_A.ndim != 2 || buf_A.shape[0] != 32 || buf_A.shape[1] != 32) {
        throw std::runtime_error("A must be a 32x32 matrix of float16");
    }
    if (buf_X.ndim != 3 || buf_X.shape[1] != 32 || buf_X.shape[2] != 32) {
        throw std::runtime_error("X must be of shape (num_batches, 32, 32)");
    }
    
    int num_batches = buf_X.shape[0];
    
    half* h_A = new half[32 * 32];
    half* h_X = new half[num_batches * 32 * 32];
    float* h_Y = new float[num_batches * 32 * 32];
    
    convert_fp16_to_half(A, h_A, 32 * 32);
    convert_fp16_to_half(X, h_X, num_batches * 32 * 32);
    
    run_cl55_tensor_core(h_A, h_X, h_Y, num_batches);
    
    auto result_copy = py::array_t<float>(buf_X.shape);
    py::buffer_info buf_result = result_copy.request();
    float* result_ptr = static_cast<float*>(buf_result.ptr);
    std::memcpy(result_ptr, h_Y, num_batches * 32 * 32 * sizeof(float));
    
    delete[] h_A;
    delete[] h_X;
    delete[] h_Y;
    
    return result_copy;
}

// Trace Projection (Gibbs-Fermi Logits)
py::array_t<float> apply_cl55_trace_projection(py::array_t<uint16_t> A, py::array_t<uint16_t> X) {
    py::buffer_info buf_A = A.request();
    py::buffer_info buf_X = X.request();
    
    if (buf_A.ndim != 2 || buf_A.shape[0] != 32 || buf_A.shape[1] != 32) {
        throw std::runtime_error("A must be a 32x32 matrix of float16");
    }
    if (buf_X.ndim != 3 || buf_X.shape[1] != 32 || buf_X.shape[2] != 32) {
        throw std::runtime_error("X must be of shape (num_batches, 32, 32)");
    }
    
    int num_batches = buf_X.shape[0];
    
    half* h_A = new half[32 * 32];
    half* h_X = new half[num_batches * 32 * 32];
    float* h_trace = new float[num_batches];
    
    convert_fp16_to_half(A, h_A, 32 * 32);
    convert_fp16_to_half(X, h_X, num_batches * 32 * 32);
    
    run_cl55_tensor_core_trace(h_A, h_X, h_trace, num_batches);
    
    auto result_copy = py::array_t<float>(num_batches);
    py::buffer_info buf_result = result_copy.request();
    float* result_ptr = static_cast<float*>(buf_result.ptr);
    std::memcpy(result_ptr, h_trace, num_batches * sizeof(float));
    
    delete[] h_A;
    delete[] h_X;
    delete[] h_trace;
    
    return result_copy;
}

// Wrapper for the continuous stream
class PyContinuousCl55Stream {
private:
    ContinuousCl55Stream* stream;
    int batches_per_frame;

public:
    PyContinuousCl55Stream(int _batches_per_frame) : batches_per_frame(_batches_per_frame) {
        stream = new ContinuousCl55Stream(_batches_per_frame);
    }
    
    ~PyContinuousCl55Stream() {
        delete stream;
    }
    
    void set_operator(py::array_t<uint16_t> A) {
        py::buffer_info buf_A = A.request();
        if (buf_A.ndim != 2 || buf_A.shape[0] != 32 || buf_A.shape[1] != 32) {
            throw std::runtime_error("A must be a 32x32 matrix of float16");
        }
        half* h_A = new half[32 * 32];
        convert_fp16_to_half(A, h_A, 32 * 32);
        stream->set_operator(h_A);
        delete[] h_A;
    }
    
    py::array_t<float> process_frame_async(py::array_t<uint16_t> X) {
        py::buffer_info buf_X = X.request();
        if (buf_X.ndim != 3 || buf_X.shape[0] != batches_per_frame || buf_X.shape[1] != 32 || buf_X.shape[2] != 32) {
            throw std::runtime_error("X must be of shape (batches_per_frame, 32, 32)");
        }
        half* h_X = new half[batches_per_frame * 32 * 32];
        convert_fp16_to_half(X, h_X, batches_per_frame * 32 * 32);
        
        const float* out_ptr = stream->process_frame_async(h_X);
        
        auto result_copy = py::array_t<float>(batches_per_frame);
        py::buffer_info buf_result = result_copy.request();
        float* result_ptr = static_cast<float*>(buf_result.ptr);
        std::memcpy(result_ptr, out_ptr, batches_per_frame * sizeof(float));
        
        delete[] h_X;
        return result_copy;
    }
};

PYBIND11_MODULE(cl55_cuda, m) {
    m.doc() = "PyBind11 module for Cl(5,5) Tensor Core acceleration";
    
    m.def("apply_cl55_tensor_flow", &apply_cl55_tensor_flow, 
          "Apply the global Cl(5,5) operator A on astronomical batches X using Tensor Cores",
          py::arg("A"), py::arg("X"));

    m.def("apply_cl55_trace_projection", &apply_cl55_trace_projection, 
          "Apply the global Cl(5,5) operator and return the Gibbs-Fermi Logit (trace) per batch",
          py::arg("A"), py::arg("X"));

    py::class_<PyContinuousCl55Stream>(m, "ContinuousCl55Stream")
        .def(py::init<int>(), py::arg("batches_per_frame"))
        .def("set_operator", &PyContinuousCl55Stream::set_operator, py::arg("A"))
        .def("process_frame_async", &PyContinuousCl55Stream::process_frame_async, py::arg("X"),
             "Process a frame asynchronously and return the trace results of the PREVIOUS frame (pipelined).");
}
