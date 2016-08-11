sig A{}
sig B{r: one A}
sig C{r':A->B}

pred P{}

assert S{}

run P 
for 4
check S for 5