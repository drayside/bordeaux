open max

--------------------------------------------------------------------------------
-- Variables and Values
--------------------------------------------------------------------------------
one sig X, Y, Z extends IntVar {}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------
run synthIntNodeI for 7 but -1..1 Int, 0 IntLit, 0 BoolLit, 0 BoolVar, 0 BinaryIntOp, 0 UnaryIntOp, 
                                       0 GT, 0 LT, 0 Xor, 0 Nand, 0 Nor, 0 BoolInvComp
run synthIntNodeI for 0 but -1..1 Int, exactly 2 ITE, exactly 2 GTE