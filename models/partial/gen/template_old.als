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
		--at most three cards on the desk
		#Round.onDesk<4
		--No card in the first Round
		--A card is put on the desk in each round
		let round1 = first | all round: Round -round1| let round'=round.prev |
								no round1.onDesk and
								one (round.onDesk - round'.onDesk) and
								--#(round.onDesk) = (#(round'.onDesk)).add[1] and
								round'.onDesk in round.onDesk  
		--Players cards and Desk cards are disjoint
		no (Player.pCards & Round.onDesk)
		--Each set has one dealer
		one Round.dealer
		--next Player to dealer is blindly betting
		one Round.blind
		one p:Player | p=Round.dealer and p.successor = Round.blind
}


sig Extra{ max_num: Number}

inst i{
		--Suit Atoms
		,
		--Number Atoms
		,

		--gt Fields
		,
		Extra=extra,
		max_num=extra->--Max Number,
		max_num=extra->Ace,
		exactly --Cards# Card,
		exactly --Players# Player,
		exactly 4 Round
}
{
--The Card Constraints
}

pred pr[]{
	one p:Player | isRoyalflush[ p.pCards+Round.onDesk] 
	
}

pred isRoyalflush[c: Card]{
				some disjoint c1,c2,c3,c4,c5:c | 
						c1.number = Extra.max_num and
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

pred p[]{}

run pr for i 
