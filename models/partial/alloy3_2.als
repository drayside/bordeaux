sig Card{
			suit: one Suit,
			number: one Number}
sig Suit{}
sig Number{}

//In case of |Legal| =< |Possible|
pred LegalCards_2[c:Card]{
		c.suit = Hearts => c.number = One
/*		c.suit = Hearts => c.number = Two
		c.suit = Hearts => c.number = Three
		c.suit = Clubs => c.number = Four
		c.suit = Clubs => c.number = Five
		c.suit = Clubs => c.number = Six
		c.suit = Spades => c.number = Seven
		c.suit = Spades => c.number = Eight
		c.suit = Spades => c.number = Nine
		c.suit = Diamonds => c.number = Ten
		c.suit = Diamonds => c.number = Jack
		c.suit = Diamonds => c.number = Queen*/}


inst i{
		Suit=Spades+Clubs+Hearts+Diamonds,
		Number=One+Two+Three+Four+Five+
		Six+Seven+Eight+Nine+Ten+Jack+
		Queen+King+Joker
		//The proposed syntax of Generator
//		Card=gen c:Card|LegalCards_1[c]
}{
	some x:Card|LegalCards_2[x]
}
		
pred p{}
run p for i
/**
Such a predicate can be converted to
		all c:Card|Legal[c] iff c in LegalCard
**/
/*pred LegalCards_1[c:Card]{
	not ( c.suit=Clubs and c.number=Joker)
	not ( c.suit=Diamonds and c.number=Joker)}

/**
Some restiction should be applied:
	No sig names 
	No calls to other Predicates and Functions
	Quantifier free?!
Another fact might put some more restriction, 
so there might be unsatisfiable.
**/


