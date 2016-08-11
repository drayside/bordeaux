module binary_implication

open property_structure as ps

abstract sig bin_prop extends prop{}

one sig bijective  extends bin_prop{}
one sig antisymmetric  extends bin_prop{}
one sig functional  extends bin_prop{}
one sig equivalence  extends bin_prop{}
one sig irreflexive  extends bin_prop{}
one sig partialOrder  extends bin_prop{}
one sig weaklyConnected  extends bin_prop{}
one sig injective  extends bin_prop{}
one sig symmetric  extends bin_prop{}
one sig stronglyConnected  extends bin_prop{}
one sig empty  extends bin_prop{}
one sig bijection  extends bin_prop{}
one sig total  extends bin_prop{}
one sig reflexive  extends bin_prop{}
one sig function  extends bin_prop{}
one sig totalOrder  extends bin_prop{}
one sig acyclic  extends bin_prop{}
one sig rootedOne  extends bin_prop{}
one sig complete  extends bin_prop{}
one sig surjective  extends bin_prop{}
one sig transitive  extends bin_prop{}
one sig preorder  extends bin_prop{}
one sig rootedAll  extends bin_prop{}
fact implication{
surjective + injective = bijective.imply
no antisymmetric.imply
no functional.imply
total + reflexive + surjective + symmetric + transitive + preorder = equivalence.imply
no irreflexive.imply
antisymmetric + total + reflexive + surjective + transitive + preorder = partialOrder.imply
no weaklyConnected.imply
no injective.imply
no symmetric.imply
//weaklyConnected + rootedAll = stronglyConnected.imply
weaklyConnected = stronglyConnected.imply
antisymmetric + functional + irreflexive + acyclic + injective + symmetric + transitive = empty.imply
bijective + total + functional + function + surjective + injective = bijection.imply
no total.imply
total + surjective = reflexive.imply
total + functional = function.imply
antisymmetric + total + reflexive + partialOrder + weaklyConnected + complete + surjective + transitive + preorder = totalOrder.imply
antisymmetric + irreflexive = acyclic.imply
weaklyConnected = rootedOne.imply
weaklyConnected = complete.imply
no surjective.imply
no transitive.imply
total + reflexive + surjective + transitive = preorder.imply
weaklyConnected + stronglyConnected = rootedAll.imply
}



-- fact from Lucy's thesis
/*fact implication{
	irreflexive + antisymmetric = acyclic.imply // correct
	weaklyConnected + symmetric + rootedAll + stronglyConnected  = complete.imply
	total + surjective  = reflexive.imply
	weaklyConnected = rootedOne.imply
	weaklyConnected + stronglyConnected = rootedAll.imply
}*/


run {}
