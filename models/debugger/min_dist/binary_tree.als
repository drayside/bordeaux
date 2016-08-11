
sig Node{
	left:  lone  Node,
	right: lone  Node}

/**
*	Binary tree valid predicates
**/
pred isAcyclic[ n: set Node, right: Node->Node, left: Node->Node ]{
  all n': n| !( n' in n'.^(right + left) )
}

pred isValidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  all n': n| ( some n'.left or some n'.right ) implies ( n'.left != n'.right )
}

pred rootedOne[ n: set Node, right: Node->Node, left: Node->Node ]{
	some n implies (one n': n| n = n'.*(right + left))
}

pred notAcyclic[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n|  n' in n'.^(right + left) 
}

pred notInvalidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n| ( n'.left = n'.right )
}
pred notValidNoCommon[ n: set Node, right: Node->Node, left: Node->Node ]{
  some n': n| ( some n'.left or some n'.right ) and ( n'.left = n'.right )
}

/**
*	The constraints for tree are not complete. Only Acyclic and no Shared Childeren
*	are considered.
**/
pred isTreeInstance[ n: set Node, right: Node->Node, left: Node->Node ]{
  isInstance[n, left,  right ]
  rootedOne[n, left, right]
  isAcyclic[n, left, right]
  isValidNoCommon[n, left, right] 
}

/**
*  The concept is the same is isTreeInstance. But (n,left, right) are making
* an instance. Moreover, due to probable bug in HOLA, kodkoda reports an exception
* due to NNF.
* It represents different kind of bugs 
**/
pred notTreeInstance[ n: set Node, right: Node->Node, left: Node->Node ]{
  	isInstance[n, left,  right ]
    rootedOne[n, left, right]
	isAcyclic[n, left, right]
	not isValidNoCommon[n, left, right] 
	//notValidNoCommon[n, left, right] 
//  ( --( notAcyclic[n, left, right] ) or
//    notValidNoCommon[n, left, right]
    --notValidNoCommon[n, left, right]
//  )
}

run notTreeInstance for 0 but exactly 3 Node

/**
*  n contains all nodes participating in left and right relations
* It deliberately prefers 'in' over '='. There might be some nodes
* not partcipating in the relations.
* Node.(left+~left+right+~right) in n
**/
pred includeInInstance[n: set Node, right: Node->Node, left: Node->Node]{
	// Node.(left+~left+right+~right) in n
	Node.left in n
	left.Node in n
	Node.right in n
	right.Node in n
}

/** W.r.t the defnition of left and right
*
**/
pred structuralConstraint[n: set Node, right: Node->Node, left: Node->Node]{
  all n': n | lone n'.left and lone n'.right
}

/**
*	isInstance means all atoms participating in the left and right 
*	have to be in node as well. isInatance is not meant to be is valid instance.
**/
pred isInstance[n: set Node, right: Node->Node, left: Node->Node]{  	
  includeInInstance[n, right, left]
  structuralConstraint[n, right, left]

}

/**
*	Tree1 = Tree2 + delta
**/
pred isDiffInstances[ n: set Node, right: Node->Node, left: Node->Node,
						n': set Node, right': Node->Node, left': Node->Node,
							n'': set Node, right'': Node->Node, left'': Node->Node ]{
{
  isInstance[n  , left  ,  right  ]
  isInstance[n' , left' ,  right' ]
--Delta is not neccessary an instance, is it?
  //includeInInstance[n'', left'',  right'']
}

	left' != left   implies ( left''= left' - left   and left'' + left = left' )  
					else no left''
	right' != right implies ( right''= right' - right and right'' + right = right') 
					else no right''
	n' != n         implies ( n'' = n' - n and n'' + n = n' )
					else no n''
}

/**
*	Is a set of (node, left, right) is a subset of another set. This is helpful
*	To find minimum or maximum delta.
**/
pred isSubDelta[ n: set Node, right: Node->Node, left: Node->Node,
						n': set Node, right': Node->Node, left': Node->Node]{
  ( n in n' and n' !in n) or 
  ( right in right' and right !in right') or 
  ( left in left' and left !in left' ) 
}

pred threeNodes[n: Node]{
	some disj n1,n2,n3: n | {n1+n2+n3} in Node
}

pred findMarginalInstances[]{
  some n: set Node, right: Node->Node, left: Node->Node,
    n': set Node, right': Node->Node, left': Node->Node,
	      n'': set Node, right'': Node->Node, left'': Node->Node |
			( //threeNodes[n] and
    		  isTreeInstance [ n , right , left ] and
    		  notTreeInstance[ n', right', left'] and
    		  isDiffInstances[ n , right , left, n', right', left', n'', right'', left'' ])
			
			and 	
			  all n1: set Node, right1: Node->Node, left1: Node->Node,
	    		n1': set Node, right1': Node->Node, left1': Node->Node,
	   			  n1'': set Node, right1'': Node->Node, left1'': Node->Node |
					( 
					  isTreeInstance [ n1 , right1 , left1 ] and
				  	  notTreeInstance[ n1', right1', left1'] and
				      isDiffInstances[ n1 , right1 , left1, n1', right1', left1', n1'', right1'', left1''])
					implies
					(#n1'' >= #n'' and  
					 ( no right'' or #left1'' >= #left'') and 
                     ( no left'' or #right1''>= #right'')) 

}

run {findMarginalInstances
no left
no right} for 0 but exactly 5 Node, 0..100 Int//, exactly 5 Bit


