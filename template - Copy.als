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
	teams: some Team
} 

sig Score { }

sig Location { }

sig Time {
	next: lone Time // ?
}

sig Team { 
	participatesIn: some Event,
	represents: one Country,
	member: some Athlete

//probably to delete
	// ? playsIn: set Performance
	// won: set Medal,
}

// Athletes
abstract sig Athlete {
	citizenOf: some Country
}
// only for testing: fact { #Athlete.citizenOf >= 2}

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

/*
 		Multiplicities
*/

fact minThreeMedalsPerEvent {
	all e:Event | #{ m: Medal | e in m.forEvent } >= 3
}
fact minThreeTeamsPerEvent {
	all e:Event | #{ t: Team | e in t.participatesIn } >= 3
}

fact minOneAthletePerCountry {
	all c:Country | #{ a: Athlete | c in a.citizenOf } >= 1
}

fact minOneTeamPerAthlete {
	all a:Athlete | #{ t: Team | a in t.member } >= 1
}

fact minOneTeamPerAthlete {
	all a:Athlete | #{ t: Team | a in t.member } >= 1
}

fact minOnePerformancePerLocation {
	all l:Location | some p:Performance | l in p.location
}

fact noLoseTime {
	all t:Time | some p:Performance | t in p.stopTime || t in p.startTime
}

fact minOnePerformancePerTeam {
	all t: Team | some p: Performance | t in p.teams
}

// don't need?
assert maxOneTimeAfterOrBeforeTime{
//	all disj t0, t1 : Time | t0.next = t1 => #{t0} <= 1 
}
//check maxOneTimeAfterOrBeforeTime


// Phases
fact noCircle_Phases {
  all p:Phase | p not in p.^next
}
fact onlyOnePredecessor_Phases {
	all p:Phase | #{ p1:Phase | p1.next = p } <= 1
}
fact onlyOnePredecessor_Phases {
	all p:Phase | #{ p1:Phase | p1.next = p } <= 1
}
fact noLoneNoShared_Phases {
	all p:Phase | one e: Event | p in e.containsPhase
}
fact allPhasesInChainInSameEvent {
	all e:Event | all p:Phase | p in e.containsPhase => p.next in e.containsPhase
}

fact oneLast_Phase{
	all e:Event | one p:Phase | p in e.containsPhase && no p.next
}

// logical facts

fact noCircle_Time{
	no t: Time | t in t.^next
}

fact noTimeLone{
	(one t:Time | no t.next) && (one t1:Time | all t2:Time | (t1 != t2) => t2.next != t1 ) 
}

fact citizenOfRepresentingCountry {
	all a:Athlete | all t: Team | a in t.member => t.represents in a.citizenOf 
}


fact noLocationUsedConcurrently{
	all disj p0,p1:Performance | p0.location = p1.location => isBefore[p0.stopTime, p1.startTime] //p1.startTime in p0.stopTime.*next 
}
fact noTeamUsedConcurrently {
	all disj p0,p1:Performance | all t: Team | t in p0.teams && t in p1.teams => isBefore[p0.stopTime, p1.startTime] //in p0.stopTime.*next
}

fact notSameStartAndStopTimeForPerformance {
//	all p:Performance | isBefore[p.startTime, p.stopTime] // p.stopTime in p.startTime.^next
}

/*
fact phasePerformanceOrder {
	all disj p1, p2: Phase | all disj prf1, prf2: Performance | 
		phaseIsBefore[p1, p2] && prf1 in p1.containsPerformance && prf2 in p2.containsPerformance
		=>isBefore[prf1.stopTime, prf2.startTime]
}
*/


// Medals

fact fromMail {
	all e: Event | 
	//Case 1
	(	#{ m: GoldMedal | e in m.forEvent} = 1 && #{ m: SilverMedal | e in m.forEvent} = 1 && #{ m: BronzeMedal | e in m.forEvent} >= 1 )
	||
	//Case 2 
	(	#{ m: GoldMedal | e in m.forEvent} = 1 && #{ m: SilverMedal | e in m.forEvent} >= 2 && #{ m: BronzeMedal | e in m.forEvent} = 0 )
	||
	//Case 3
	(	#{ m: GoldMedal | e in m.forEvent} = 2 && #{ m: SilverMedal | e in m.forEvent} = 0 && #{ m: BronzeMedal | e in m.forEvent} >= 1 )
	||
	//Case 4
	(	#{ m: GoldMedal | e in m.forEvent} >= 3 && #{ m: SilverMedal | e in m.forEvent} = 0 && #{ m: BronzeMedal | e in m.forEvent} = 0 )
	
}

fact MedalsForTeamsInEvent {
	all m: Medal | all e: Event | all t: Team | e in m.forEvent && t in m.forTeam => e in t.participatesIn
}

fact onlyOneMedalperTeamEvent {
	all e: Event | all t: Team | lone m:Medal | e in m.forEvent && e in t.participatesIn && t in m.forTeam
}

fact equalScoreEqualMedal {
//	all e: Performance | all disj t1, t2: Team | t1 in e.teams && t2 in e.teams && t1.score.value = t2.score.value 
}


//Athletes
fact noAthleteInTwoCountriesTeams {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && t1.represents != t2.represents
}
fact noAthleteInTwoTeamsPerEvent {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && (t1.participatesIn & t2.participatesIn) = none
}

// Teams
fact noTeamsInDifferentDisciplines {
	all d1, d2: Discipline | all t: Team | teamInDiscipline[t, d1] && teamInDiscipline[t, d2] => d1 = d2
}

fact onlyThreeTeamsPerDisciplinePerCountry {
	all c: Country | all d: Discipline | #{ t: Team | c in t.represents && teamInDiscipline[t, d] } <= 3
}


fact {
	some d: Discipline | #d.containsEvent > 1
}

/* Figure Skating */

pred show {}
run show for 20

/* 
	OUR Predicates
*/

pred teamInDiscipline[t: Team, d: Discipline] { t.participatesIn & d.containsEvent != none }



// Predicates


// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] { t2 in t1.^next }

// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] { p2 in p1.^next }

// True iff m is a gold medal.
pred isGoldMedal[m : Medal] { m in GoldMedal }

// True iff m is a silver medal.
pred isSilverMedal[m : Medal] { m in SilverMedal }

// True iff m is a bronze medal.
pred isBronzeMedal[m: Medal] { m in BronzeMedal }

// True iff t is among the best teams in phase p.
//pred isAmongBest[t: Team, p: Phase] { ... }

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
fun getMedals[e: Event] : set Medal {  }

// Returns the start time of the performance p.
fun getStart[p : Performance] : Time { p.startTime }

// Returns the end time of the performance p.
fun getEnd[p: Performance] : Time { p.endTime }

// Returns the location of the performance p.
fun getLocation[p: Performance] : Location { p.location } 

// Returns all the teams which paricipate in the performance p.
fun getParticipants[p: Performance] : set Team { p.teams }

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { t.member }

// Returns the team which won the medal m.
//fun getWinner[m: Medal] : Team { ... }


*/
