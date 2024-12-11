# frame_protocol_FV

There is an assertion named SOL_SHOULD_FAIL_SANITY_CHECK (sanity check) was failed. The reason it was failed due to sop_out and eop_out signals. As both signals are high for consecutive cycles, it is not satisfying the SOL_SHOULD_FAIL_SANITY_CHECK assertion. Expecting this assertion to fail as it is a sanity check to check the confidence of tool and environment.
