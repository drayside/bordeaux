open util/ordering[Round] 

sig Suit{}
sig Number{gt:lone Number}

sig Card{
			suit: one Suit,
			number: one Number}

sig Player{
			pCards: set Card,
			chips: one Int,
			successor: one Player}

sig Round{
			onDesk:set Card,
			dealer: one Player,
			blind: one Player
}

fact playing_rules{
		--No body plays by himself
		all p:Player | p.successor != p
		--Playing in a circular arrangment
		all p:Player | p.^successor = Player
		--each player have to have exactly two cards
		all p:Player | #p.pCards = 2
		--Pocket cards are shared
		all disjoint p1,p2:Player | no (p1.pCards & p2.pCards )
}

fact round_rules{
		--at most four rounds
		#Round = 4
		--No card in the first Round
		--A card is put on the desk in each round
		let round1 = first | all round: Round -round1| let round'=round.prev |
								no round1.onDesk and
								#(round.onDesk) = (#(round'.onDesk)).add[1] and
								round'.onDesk in round.onDesk  
		--Players cards and Desk cards are disjoint
		no (Player.pCards & Round.onDesk)
		--Each set has one dealer
		one Round.dealer
		--next Player to dealer is blindly betting
		one Round.blind
		one p:Player | p=Round.dealer and p.successor = Round.blind
}

inst i{
		Suit=Spades+Clubs+Hearts+Diamonds,
		Number=Ace+Two/*+Three+Four+Five+
		Six+Seven+Eight*/+Nine+Ten+Jack+
		Queen+King+Joker,
		gt=	Ace->Two+Two/*->Three+Three->Four+
				Four->Five+Five->Six+Six->Seven+
				Seven->Eight+Eight*/->Nine+Nine->Ten+
				Ten->Jack+Jack->Queen+Queen->King+
				King->Ace,
		exactly 16 Card,
		exactly 4 Player,
		exactly 4 Round
		//The proposed syntax of Generator
//		Card=gen c:Card|LegalCards_1[c]
}
{
	--allcards are distinct
	all c1: Card | no c2:Card-c1 | c1.number=c2.number and c1.suit =c2.suit
	--card set does not include Joker
	//some joker:Number | joker=Joker and whole_deck[joker]

all c: Card | c.number != Joker

	--Tsting area
//	some ace:Number | some  c: set Card | ace= Ace and 	isRoyalflush[ace,c]
//	some  c: set Card | isStraight[c] and #c =5

}
		
pred whole_deck[n:Number]{
				all c: Card | c.number != n
}

pred isRoyalflush[ace:Number,c: Card]{
				some disjoint c1,c2,c3,c4,c5:c | 
						c1.number = ace and
						c2.number = c1.number.~gt and
						c3.number = c2.number.~gt and
						c4.number = c3.number.~gt and
						c5.number = c4.number.~gt and
						c1.suit = c2.suit and
						c2.suit = c3.suit and
						c4.suit = c5.suit and
						c5.suit = c.suit and
						one c1.suit	
}

pred isStraightflush[c: Card]{
			some disjoint c1,c2,c3,c4,c5:c | 
			c2.number = c1.number.~gt and
			c3.number = c2.number.~gt and
			c4.number = c3.number.~gt and
			c5.number = c4.number.~gt and
			c1.suit = c2.suit and
			c2.suit = c3.suit and
			c4.suit = c5.suit and
			c5.suit = c.suit and
			one c1.suit	
}

pred isFourOfaKind[c: Card]{
			some disjoint c1,c2,c3,c4:c | 
			c2.number = c1.number and
			c3.number = c2.number and
			c4.number = c3.number 
}

pred isFullHouse[c:Card]{
		some disjoint c1,c2,c3,c4,c5:c | 			
		c2.number = c1.number and
		c3.number = c2.number and
		c4.number = c5.number 
}

pred isFull[c:Card]{
		some disjoint c1,c2,c3,c4,c5:c | 
		c1.suit=c2.suit and
		c2.suit=c3.suit and
		c3.suit=c4.suit and
		c4.suit=c5.suit 
}

pred isStraight[c: Card]{
			some disjoint c1,c2,c3,c4,c5:c | 
			c2.number = c1.number.~gt and
			c3.number = c2.number.~gt and
			c4.number = c3.number.~gt and
			c5.number = c4.number.~gt 
}

pred isThreeOfaKind[c: Card]{
			some disjoint c1,c2,c3:c | 
			c2.number = c1.number and
			c3.number = c2.number 
}

pred isTwoPair[c:Card]{
		some disjoint c1,c2,c4,c5:c | 			
		c2.number = c1.number and
		c4.number = c5.number 
}

pred isOnePair[c:Card]{
		some disjoint c1,c2:c | 			
		c2.number = c1.number 
}

pred pr[]{}

run pr for i
