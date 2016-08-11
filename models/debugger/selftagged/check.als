open relational_properties_tagged

sig Right{}
sig Left{r: set Right}

assert ac{
{bijection[r, Left, Right] implies totalOrder[r, Left, Right]}
}

check ac

check {totalOrder[r, Left, Right] implies bijection[r, Left, Right]}
