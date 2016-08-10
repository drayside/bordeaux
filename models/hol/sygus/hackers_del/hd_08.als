/**
 * NOTE: make sure to set "Options -> Prevent overflows" to "No"
 *
 * Form a mask that identifies the trailing zeros
 */
module hd_08

open hd[hd08]

one sig Lit1 extends IntLit {}
fact {
  IntLit<:val = Lit1->1
}

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------
fun hd08[x: Int]: Int {
  bvand[bvnot[x], bvsub[x, 1]]
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-08-d0-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: [literals, bw(5)]} Int, 4 IntVarVal,
                            exactly 1 BvSub, exactly 1 BvAnd, exactly 1 BvNot

-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-08-d1-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 32, atoms: bw(5)} Int, 4 IntVarVal,
                            exactly 1 BvAdd, exactly 1 BvSub, exactly 1 BvNot, exactly 1 BvNeg, exactly 1 BvAnd, exactly 1 BvOr, exactly 1 BvXor


-- (https://github.com/rishabhs/sygus-comp14/blob/master/benchmarks/hackers_del/hd-08-d5-prog.sl)
run synthIntNodeI for 0 but {bitwidth: 16, atoms: bw(5)} Int, 4 IntVarVal,
                            exactly 3 BinaryIntOp, exactly 2 UnaryIntOp
