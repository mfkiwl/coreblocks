class VectorParameters:
    def __init__(self, *, vlen : int, elen : int, vrp_count=40):
        self.elen = elen
        self.vlen = vlen
        self.vrp_count = vrp_count
        self.vrp_count_bits = log2_int(self.vrp_count)

        self.bytes_in_vlen = self.vlen // 8
        self.bytes_in_elen = elen // 8

        self.register_bank_count = 4

        accepted_elens = {8,16,32,64}
        if self.elen not in accepted_elens:
            raise ValueError(f"Wrong ELEN value. Got: {self.elen}, expected one of: {accepted_elens}")

        if self.vlen % self.elen !=0:
            raise ValueError(f"Wrong vectors parameters. VLEN should be divisable by ELEN")

        self.elems_in_vlen = self.vlen // self.elen

        if self.elems_in_vlen%self.v_params.register_bank_count != 0:
            raise ValueError("Number of elements in vector register not divisable by number of banks.")

        self.elems_in_bank = self.elems_in_vlen // self.v_params.register_bank_count
        self.elems_in_bank_bits = log2_int(self.elems_in_bank)