`timescale 1ns / 1ps

module cmos_estimator (
    input wire clk,
    input wire rst_n,
    
    // Interface to pixel stream
    input wire [15:0] pixel_val_in,      // New observation
    input wire pixel_valid,              // High when pixel is valid
    
    // Oracle parameters (could be registers in real HW)
    input wire [31:0] c_t,               // Threshold for admission
    input wire [31:0] eps_t,             // Temp parameter
    input wire [15:0] rho,               // Discount factor
    
    // Outputs
    output reg [15:0] mu_out,            // Filtered background estimation
    output reg is_cr,                    // Cosmic Ray Flag
    output reg out_valid                 // Valid output flag
);

    // Q16.16 Fixed point representation for internal states
    reg [31:0] mu_state;
    reg [31:0] N_state;
    reg initialized;
    
    // Wires for combinatorial outputs (Bregman divergences and combinational logic)
    wire [31:0] D_t;
    wire [31:0] r_t; // admission responsibility
    
    // Stub modules for Bregman Divergence and Fermi-Boltzmann logit
    // In actual hardware, these would use lookup tables, DSP multipliers, or CORDIC
    
    bregman_divergence_core div_core (
        .x_in({16'b0, pixel_val_in}), 
        .mu_in(mu_state),
        .D_out(D_t)
    );
    
    fermi_boltzmann_admission fb_core (
        .D_t(D_t),
        .c_t(c_t),
        .eps_t(eps_t),
        .r_t(r_t)
    );
    
    wire is_cosmic_ray = (r_t < (32'h0000_8000)); // r_t < 0.5 in Q16.16
    
    // W_prime = rho * N_state + r_t
    wire [31:0] W_a = (N_state * rho) >> 16; 
    wire [31:0] W_prime = W_a + r_t;
    
    // delta = x - mu
    wire signed [31:0] delta = {16'b0, pixel_val_in} - mu_state;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mu_state <= 32'b0;
            N_state <= 32'b0;
            initialized <= 1'b0;
            mu_out <= 16'b0;
            is_cr <= 1'b0;
            out_valid <= 1'b0;
        end else begin
            if (pixel_valid) begin
                if (!initialized) begin
                    mu_state <= {16'b0, pixel_val_in};
                    N_state <= 32'b0;
                    initialized <= 1'b1;
                    mu_out <= pixel_val_in;
                    is_cr <= 1'b0;
                    out_valid <= 1'b1;
                end else begin
                    
                    is_cr <= is_cosmic_ray;
                    out_valid <= 1'b1;
                    
                    if (W_prime > 0) begin
                        // This division would be pipelined in real HW
                        // mu_state += (r_t / W_prime) * delta
                        
                        // For illustration, a simplistic single-cycle update (not synthesizable cleanly without a divider IP)
                        // In practice, we use a reciprocal LUT for 1/W_prime
                        reg signed [31:0] update_term;
                        update_term = ((r_t << 16) / W_prime * delta) >> 16;
                        
                        mu_state <= mu_state + update_term;
                        mu_out <= (mu_state + update_term) >> 16;
                    end
                    
                    N_state <= W_prime;
                end
            end else begin
                out_valid <= 1'b0;
            end
        end
    end

endmodule

// Dummy combinatorial stubs to pass syntax checking
module bregman_divergence_core(
    input [31:0] x_in,
    input [31:0] mu_in,
    output [31:0] D_out
);
    // Gaussian approx for stub
    wire signed [31:0] diff = x_in - mu_in;
    assign D_out = (diff * diff) >> 17; // x^2 / 2
endmodule

module fermi_boltzmann_admission(
    input [31:0] D_t,
    input [31:0] c_t,
    input [31:0] eps_t,
    output [31:0] r_t
);
    // Simple thresholding for the stub to emulate sigmoid
    assign r_t = (D_t > c_t) ? 32'h0000_0000 : 32'h0001_0000;
endmodule
