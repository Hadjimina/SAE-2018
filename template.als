/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */

sig Discipline { 
	containsEvent: some Event //not shared
}



sig Event {
	containsPhase: some Phase, // not shared
	//participant: some Team // three or more
}

sig Phase { 
	next: lone Phase, // ?
	containsPerformance: some Performance // not shared
}

sig Performance {
	location: one Location, // can be shared
	startTime: one Time, // can be shared
	stopTime: one Time, // "
	score: one Score, // not shared
	// team ?
} 

sig Score { }

sig Location { }

sig Time {
	next: lone Time // ?
}

sig Team { 
	participatesIn: some Event,
	// ? playsIn: set Performance
	represents: one Country,
	// won: set Medal,
	member: some Athlete
}

// Athletes
abstract sig Athlete {
	citizenOf: some Country
}

sig FemaleAthlete extends Athlete {}
sig MaleAthlete extends Athlete {}

sig Country {}






// Medals
abstract sig Medal { 
	forEvent: one Event,
	forTeam: one Team
}


sig GoldMedal extends Medal {}
sig SilverMedal extends Medal {}
sig BronzeMedal extends Medal {}

/* 
	FACTS
*/

// not shared Facts - Rauten
fact {
	all disj d1, d2: Discipline | all e: Event | e in d1.containsEvent implies e not in d2.containsEvent
}
fact {
	all disj e1, e2: Event | all p: Phase | p in e1.containsPhase implies p not in e2.containsPhase
}
fact {
	all disj e1, e2: Phase | all p: Performance | p in e1.containsPerformance implies p not in e2.containsPerformance
}
fact {
	all disj p1, p2: Performance | p1.score != p2.score
}

// multiplicities
fact minThreeMedalsPerEvent {
	all e:Event | #{ m: Medal | e in m.forEvent } >= 3
}
fact minThreeTeamsPerEvent {
	all e:Event | #{ t: Team | e in t.participatesIn } >= 3
}
// fact

pred show {}
run show for 10

/*
 * Predicates
 

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] { ... }

// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] { ... }

// True iff m is a gold medal.
pred isGoldMedal[m : Medal] { ... }

// True iff m is a silver medal.
pred isSilverMedal[m : Medal] { ... }

// True iff m is a bronze medal.
pred isBronzeMedal[m: Medal] { ... }

// True iff t is among the best teams in phase p.
pred isAmongBest[t: Team, p: Phase] { ... }

/*
 * Functions
 

// Returns all the events offered by the discipline d.
fun getEvents[d: Discipline] : set Event { ... } 

// Returns all the teams which participate in the event e.
fun getEventParticipants[e: Event] : set Team { ... }

// Returns all the phases of the event e.
fun getPhases[e: Event] : set Phase { ... }

// Returns all the performances which take place within the phase p.
fun getPerformances[p: Phase] : set Performance { ... }

// Returns the set of medals handed out for the event e.
fun getMedals[e: Event] : set Medal { ... }

// Returns the start time of the performance p.
fun getStart[p : Performance] : Time { ... }

// Returns the end time of the performance p.
fun getEnd[p: Performance] : Time { ... }

// Returns the location of the performance p.
fun getLocation[p: Performance] : Location { ... } 

// Returns all the teams which paricipate in the performance p.
fun getParticipants[p: Performance] : set Team { ... }

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { ... }

// Returns the team which won the medal m.
fun getWinner[m: Medal] : Team { ... }


*/
