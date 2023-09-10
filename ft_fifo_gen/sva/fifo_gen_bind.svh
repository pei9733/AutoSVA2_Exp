bind fifo_gen fifo_gen_prop
	#(
		.INFLIGHT_IDX (INFLIGHT_IDX),
		.SIZE (SIZE),
		.ASSERT_INPUTS (0)
	) u_fifo_gen_sva(.*);