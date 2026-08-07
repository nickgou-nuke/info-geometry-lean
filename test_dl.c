#include <stdio.h>
#include <dlfcn.h>
#include <stdint.h>

int main() {
    void* handle = dlopen("./backend/cuda/build/libzorn_cuda.so", RTLD_LAZY);
    if (!handle) {
        printf("dlopen failed: %s\n", dlerror());
        return 1;
    }
    printf("Loaded libzorn_cuda.so\n");
    return 0;
}
