sig A,C,E{}

sig B{
 As: set A,
 AC: As  -> one C,
 AH : E one->one As
}

fact {
	all disj b,b':B| b.As !=b'.As or b.AC!=b'.AC
}

pred p[]{}

inst i{3, exactly 1 A, exactly 2 C, exactly 1 B, exactly 0 E}

run p for i
//3 but exactly 1 A, exactly 2 C, exactly 1 B, exactly 0 E
