#include <pybind11/pybind11.h>
#include <pybind11/numpy.h>

namespace py = pybind11;

// Декларация на външната функция от GibbsFermiSensor.cu
extern void launch_gibbs_fermi_sensor(const double* h_raw, double* h_clean, int N, double t);

// Python Wrapper
py::array_t<double> filter_twistor_image(py::array_t<double> input_array, double time_boost) {
    py::buffer_info buf = input_array.request();
    int N = buf.size;

    const double* raw_ptr = static_cast<const double*>(buf.ptr);

    // Създаване на изходния NumPy масив
    auto result = py::array_t<double>(buf.shape);
    py::buffer_info res_buf = result.request();
    double* clean_ptr = static_cast<double*>(res_buf.ptr);

    // Извикване на CUDA ядрото
    launch_gibbs_fermi_sensor(raw_ptr, clean_ptr, N, time_boost);

    return result;
}

PYBIND11_MODULE(zorn_cuda, m) {
    m.doc() = "Twistor ISP Gibbs-Fermi Sensor implemented in CUDA";
    m.def("filter", &filter_twistor_image, "Apply Tomita-Takesaki modular flow filter to an image",
          py::arg("image"), py::arg("time_boost") = 0.1);
}
