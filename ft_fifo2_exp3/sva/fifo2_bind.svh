bind fifo2 fifo2_prop
	#(
		.INFLIGHT_IDX (INFLIGHT_IDX),
		.SIZE (SIZE),
		.ASSERT_INPUTS (0)
	) u_fifo2_sva(.*);