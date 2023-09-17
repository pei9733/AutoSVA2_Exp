/*
RULES:
SVA assertions are written within a property file, but DO NOT rewrite the tlb interface and DO NOT add includes in the property file (as we already have them in the property file).
DO NOT declare properties; DECLARE assertions named asgpt__<NAME>: assert property (<EXPRESSION>).
DO NOT use [] at the end of assertion NAME. Do not add @(posedge clk) to EXPRESSION.
Assertions must be as high-level as possible, to avoid repeating implementation details.
Above each assertion, write a comment explaining behavior being checked.

$countones(bitarray) returns the number of ONES in bitarray.
&bitarray means that ALL the bits  are ONES.
!(&bitarray) means it's NOT TRUE that ALL the bits are ONES, i.e., SOME of the bits are ZEROS.
|bitarray means that SOME bits is ONES.
!(|bitarray) means that NONE of the bits are ONES, i.e., ALL the bits are ZEROS.

Same-cycle assertions (|->): the precondition and postcondition are evaluated in the same cycle.
Next-cycle assertions (|=>): the precondition is evaluated in the current cycle and the postcondition in the next cycle.
Signals ending in _q are registers: the assigned value changes in the next cycle.
Signals NOT ending in _q are wires: the assigned value changes in the same cycle.
The assigned value to wires (signals NOT ending in _q) can be referenced in the current cycle.
USE a same-cycle assertion (|->) to reason about behavior ocurring in the same cycle.
USE a next-cycle assertion (|=>) to reason about behavior ocurring in the next cycle, for example, the updated value of a _q.
USE same-cycle assertions (|->) when reasoning about the assigned value of wires (signals NOT ending in _q).
USE next-cycle assertions (|=>) when reasoning about the data being added to _q.
DO NOT USE $past() in preconditions, ONLY in postconditions.
DO NOT USE $past() on the postcondition of same-cycle assertion (|->).
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of wires.
On the postcondition of next-cycle assertions (|=>), DO NOT USE $past() to refer to the updated value of _q.
On the postcondition of next-cycle assertions (|=>), USE $past() to refer to the value of the _q on the cycle of the precondition, before the register update.
Assertions without precondition DO NOT use |->

DO NOT use foreach loops in assertions; Instead, use generate loops.
Interface signals are those declared as input or output, in the module interface.
Internal signals are declared within the tlb implementation body.
Referencing internal signals in the property file ALWAYS requires prepending tlb before the signal name as tlb.<internal_signal>
NEVER reference internal signals without tlb as prefix, e.g., tlb.<internal_signal>


TASK:
Write SVA assertions to check correctness of ALL the functionality of tlb but the reset behavior.
DO NOT answer anything except for the property file, ONLY write comments within the property file.
*/


module tlb import ariane_pkg::*; #(
      parameter int unsigned TLB_ENTRIES = 4,
      parameter int unsigned ASID_WIDTH  = 1
  )(
    input  logic                    clk_i,    
    input  logic                    rst_ni,   
    input  logic                    flush_i,  
    
    
    input  tlb_update_t             update_i,
    
    input  logic                    lu_access_i,
    input  logic [ASID_WIDTH-1:0]   lu_asid_i,
    input  logic [riscv::VLEN-1:0]  lu_vaddr_i,
    output riscv::pte_t             lu_content_o,
    input  logic [ASID_WIDTH-1:0]   asid_to_be_flushed_i,
    input  logic [riscv::VLEN-1:0]  vaddr_to_be_flushed_i,
    output logic                    lu_is_2M_o,
    output logic                    lu_is_1G_o,
    output logic                    lu_hit_o
);

    
    struct packed {
      logic [ASID_WIDTH-1:0] asid;
      logic [riscv::VPN2:0]  vpn2;
      logic [8:0]            vpn1;
      logic [8:0]            vpn0;
      logic                  is_2M;
      logic                  is_1G;
      logic                  valid;
    } [TLB_ENTRIES-1:0] tags_q, tags_n;

    riscv::pte_t [TLB_ENTRIES-1:0] content_q, content_n;
    logic [8:0] vpn0, vpn1;
    logic [riscv::VPN2:0] vpn2;
    logic [TLB_ENTRIES-1:0] lu_hit;     
    logic [TLB_ENTRIES-1:0] replace_en; 
    
    
    
    always_comb begin : translation
        vpn0 = lu_vaddr_i[20:12];
        vpn1 = lu_vaddr_i[29:21];
        vpn2 = lu_vaddr_i[30+riscv::VPN2:30];

        
        lu_hit       = '{default: 0};
        lu_hit_o     = 1'b0;
        lu_content_o = '{default: 0};
        lu_is_1G_o   = 1'b0;
        lu_is_2M_o   = 1'b0;

        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
            
            
            if (tags_q[i].valid && ((lu_asid_i == tags_q[i].asid) || content_q[i].g)  && vpn2 == tags_q[i].vpn2) begin
                
                if (tags_q[i].is_1G) begin
                    lu_is_1G_o = 1'b1;
                    lu_content_o = content_q[i];
                    lu_hit_o   = 1'b1;
                    lu_hit[i]  = 1'b1;
                
                end else if (vpn1 == tags_q[i].vpn1) begin
                    
                    
                    if (tags_q[i].is_2M || vpn0 == tags_q[i].vpn0) begin
                        lu_is_2M_o   = tags_q[i].is_2M;
                        lu_content_o = content_q[i];
                        lu_hit_o     = 1'b1;
                        lu_hit[i]    = 1'b1;
                    end
                end
            end
        end
    end



    logic asid_to_be_flushed_is0;  
    logic vaddr_to_be_flushed_is0;  
    logic  [TLB_ENTRIES-1:0] vaddr_vpn0_match;
    logic  [TLB_ENTRIES-1:0] vaddr_vpn1_match;
    logic  [TLB_ENTRIES-1:0] vaddr_vpn2_match;

    assign asid_to_be_flushed_is0 =  ~(|asid_to_be_flushed_i);
    assign vaddr_to_be_flushed_is0 = ~(|vaddr_to_be_flushed_i);

	  
    
    
    always_comb begin : update_flush
        tags_n    = tags_q;
        content_n = content_q;

        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin

            vaddr_vpn0_match[i] = (vaddr_to_be_flushed_i[20:12] == tags_q[i].vpn0);
            vaddr_vpn1_match[i] = (vaddr_to_be_flushed_i[29:21] == tags_q[i].vpn1);
            vaddr_vpn2_match[i] = (vaddr_to_be_flushed_i[38:30] == tags_q[i].vpn2);

            if (flush_i) begin
                
                
        				if (asid_to_be_flushed_is0 && vaddr_to_be_flushed_is0 )
                    tags_n[i].valid = 1'b0;
                
                else if (asid_to_be_flushed_is0 && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_2M) ) && (~vaddr_to_be_flushed_is0))
                    tags_n[i].valid = 1'b0;
                
				        else if ((!content_q[i].g) && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_2M)) && (asid_to_be_flushed_i == tags_q[i].asid) && (!vaddr_to_be_flushed_is0) && (!asid_to_be_flushed_is0))
				          	tags_n[i].valid = 1'b0;
                
				        else if ((!content_q[i].g) && (vaddr_to_be_flushed_is0) && (asid_to_be_flushed_i == tags_q[i].asid) && (!asid_to_be_flushed_is0))
				        	  tags_n[i].valid = 1'b0;
            
            end else if (update_i.valid & replace_en[i]) begin
                
                tags_n[i] = '{
                    asid:  update_i.asid,
                    vpn2:  update_i.vpn [18+riscv::VPN2:18],
                    vpn1:  update_i.vpn [17:9],
                    vpn0:  update_i.vpn [8:0],
                    is_1G: update_i.is_1G,
                    is_2M: update_i.is_2M,
                    valid: 1'b1
                };
                
                content_n[i] = update_i.content;
            end
        end
    end

    
    
    
    logic[2*(TLB_ENTRIES-1)-1:0] plru_tree_q, plru_tree_n;
    always_comb begin : plru_replacement
        plru_tree_n = plru_tree_q;
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
            automatic int unsigned idx_base, shift, new_index;
            
            if (lu_hit[i] & lu_access_i) begin
                
                for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
                  idx_base = $unsigned((2**lvl)-1);
                  
                  shift = $clog2(TLB_ENTRIES) - lvl;
                  
                  new_index =  ~((i >> (shift-1)) & 32'b1);
                  plru_tree_n[idx_base + (i >> shift)] = new_index[0];
                end
            end
        end
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        for (int unsigned i = 0; i < TLB_ENTRIES; i += 1) begin
            automatic logic en;
            automatic int unsigned idx_base, shift, new_index;
            en = 1'b1;
            for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
                idx_base = $unsigned((2**lvl)-1);
                
                shift = $clog2(TLB_ENTRIES) - lvl;

                
                new_index =  (i >> (shift-1)) & 32'b1;
                if (new_index[0]) begin
                  en &= plru_tree_q[idx_base + (i>>shift)];
                end else begin
                  en &= ~plru_tree_q[idx_base + (i>>shift)];
                end
            end
            replace_en[i] = en;
        end
    end

    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            tags_q      <= '{default: 0};
            content_q   <= '{default: 0};
            plru_tree_q <= '{default: 0};
        end else begin
            tags_q      <= tags_n;
            content_q   <= content_n;
            plru_tree_q <= plru_tree_n;
        end
    end


    
endmodule


