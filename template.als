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
	//winner: one Team
} 

sig Score {
	score:one Int,
	forTeam: one Team
}

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

// COMPOSITION

//Enforces composition relation between Discipline and event
fact CompositionDisciplineEvent{
	all disj d1, d2: Discipline | all e: Event | e in d1.containsEvent implies e not in d2.containsEvent
}
//Enforces composition relation between event and phase
fact CompositionEventPhase{
	all disj e1, e2: Phase | all p: Performance | p in e1.containsPerformance implies p not in e2.containsPerformance
}
//Enforces composition relation between performance and score
fact CompositionPerformanceScore {
	all disj p1, p2: Performance | p1.score != p2.score
}

fact noPhaseWithoutEvent {
	all p: Phase | some e: Event | p in e.containsPhase
}

fact noEventWithoutDiscipline {
	all e: Event | some d: Discipline | e in d.containsEvent 
}

fact noScoreWithoutPerformance {
	all s: Score | some p: Performance | s in p.score
}

fact noPerformanceWithoutPhase {
	all p:Performance | some ph: Phase | p in ph.containsPerformance
}


/* was already implied 
assert noSharedPhase {
	all disj e1, e2: Event | all p: Phase | p in e1.containsPhase implies p not in e2.containsPhase
}
check noSharedPhase
*/


/* 
	MULITPLICITIES
*/ 
//Enoforces the multiplicities constraints from the UML model
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



/* was already implied //DELETE ? TODO
assert minThreeMedalsPerEvent {
	all e:Event | #{ m: Medal | e in m.forEvent } >= 3
}
check minThreeMedalsPerEvent
*/

/* don't need? //DELETE ? TODO
fact maxOneTimeAfterOrBeforeTime{
	all disj t0, t1 : Time | t0.next = t1 => #{t0} <= 1 
}
check maxOneTimeAfterOrBeforeTime
*/

// Phases
// Enfoces facts regarding the phases
fact noCirclePhases {
  all p:Phase | p not in p.^next
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
//also implies that every Event has at least one phase
fact oneLast_Phase{
	all e:Event | one p:Phase | p in e.containsPhase && no p.next
}


// Time
// Enfoces facts regarding the time
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
	all disj p0,p1:Performance | p0.location = p1.location => isBefore[p0.stopTime, p1.startTime] 
}
fact noTeamUsedConcurrently {
	all disj p0,p1:Performance | all t: Team | t in p0.teams && t in p1.teams => isBefore[p0.stopTime, p1.startTime]
}

// No Instance found, Too big of a model or to restrictive
fact notSameStartAndStopTimeForPerformance {
	 all p:Performance | isBefore[p.startTime, p.stopTime] 
}

fact phasePerformanceOrder {
	all disj p1, p2: Phase | all disj prf1, prf2: Performance | 
		phaseIsBefore[p1, p2] && prf1 in p1.containsPerformance && prf2 in p2.containsPerformance
		=>isBefore[prf1.stopTime, prf2.startTime]
}




// Medals
// Enfoces facts regarding the medals
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
fact equalScoreEqualMedal { // What for answer maybe not need for us b.c. different score implementation in figure skating //TODO
//	all e: Performance | all disj t1, t2: Team | t1 in e.teams && t2 in e.teams && t1.score.value = t2.score.value 
}

//Athletes
// Enfoces facts regarding the athletes
fact noAthleteInTwoCountriesTeams {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && t1.represents != t2.represents
}
fact noAthleteInTwoTeamsPerEvent {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && (t1.participatesIn & t2.participatesIn) = none
}

// Teams
// Enfoces facts regarding the teams
fact noTeamsInDifferentDisciplines {
	all d1, d2: Discipline | all t: Team | teamInDiscipline[t, d1] && teamInDiscipline[t, d2] => d1 = d2
}

fact onlyThreeTeamsPerDisciplinePerCountry {
	all c: Country | all d: Discipline | #{ t: Team | c in t.represents && teamInDiscipline[t, d] } <= 3
}

//Score
// Enfoces facts regarding the score
fact noScoreWOPerformance{
	all s:Score | some p:Performance | p.score = s
}

fact winnerOfLastPhaseGetsGold{ //TODO
/*	all t:Team | all p:Phase | all s:Score | one g:GoldMedal | #{p.next}=0 && t in getPerformances[p].teams 
	&& s in getPerformances[p].score && s.score >= getPerformances[p].score.score&& t in s.forTeam => t in g.forTeam*/
}



// For testing
fact testLocationSharing { // SLOWING DOWN ENORMOUSLY // OVERRESTRICTED SOMEWHERE ??
	some disj p1,p2:Performance | p1.location = p2.location
}
fact {
//	all a:Athlete | some disj t1, t2: Team | a in t1.member && a in t2.member
} 
fact {
//	no c: Country | no t: Team | c in t.represents
}

fact {
	//	some d: Discipline | #d.containsEvent > 1
}



/* 

		Figure Skating 


//Signatures required for the specific part
one sig FigureSkating extends Discipline {}
//{ #FigureSkating <= 1}

//one ?? correct
one sig IceDancing extends Event {}

sig ShortProgram extends FigureSkatingPhase {}

abstract sig FigureSkatingPhase extends Phase {
	participants: some Team
}

sig FreeSkatingProgram extends FigureSkatingPhase {}

sig FigureSkatingScore extends Score{
	TechScore: one Int,
	PresScore: one Int
	
}

// facts regarding the Ice Dancing pairs
fact onlyPairsInIceDancing { // use sig instead ?
	all t:Team | all e:Event | one m:MaleAthlete | one f:FemaleAthlete |  e in IceDancing && e in t.participatesIn 
	=> #t.member = 2 && m in t.member && f in t.member
}
fact notTwoInstancesOfSamePair{ //TODO CHECK THIS
	no disj a1,a2: Athlete | some disj t1,t2:Team | all e:Event | e in IceDancing &&  e in IceDancing && e in t1.participatesIn && e in t2.participatesIn &&
	a1 in t1.member && a1 in t2.member && a2 in t1.member && a2 in t2.member && t1 != t2

//	all t1,t2:Team| all e:Event | all m:MaleAthlete | all f:FemaleAthlete | e in IceDancing && e in t1.participatesIn && e in t2.participatesIn && //DELETE TODO
//	m in t1.member && m in t2.member && f in t1.member && f in t2.member => t1 = t2

//	all m:MaleAthlete | all f:FemaleAthlete |  all e:Event  | #{t:Team | m in t.member && f in t.member &&  e in IceDancing && e in t.participatesIn} = 1
}


// Enforces that IceDancing events are only held in the figure skating discipline
fact IceDancingOnlyInFigureSkating{	
	{IceDancing} = FigureSkating.containsEvent
}

// impled by IceDancingOnlyInOneDisciplinem and onlyThreeTeamsPerDisciplinePerCountry //DELETE TODO
fact OnlyThreeTeamsPerCountry{
//	all e:Event | all t:Team | all c:Country | c in t.represents && e in t.participatesIn && e in IceDancing 
}

// Enforces constraint regarding the free and short program (i.e. phases)
fact TwentyTwoPairsInShortProgram{ 
 	all sp:ShortProgram | #{ t:Team | t in sp.participants} = 5 //change to 22 TODO
}
fact SixteenPairsInFreeSkatingProgram {
	all f: FreeSkatingProgram | # { t: Team | t in f.participants } < 5 // change to 16 TODO
}

fact oneShortOneFreePerIceEvent {
	all i: IceDancing | one s: ShortProgram | one f: FreeSkatingProgram | s in i.containsPhase && f in i.containsPhase
}
// only correct because of one sig IceDancing Constraint
fact ShortAndFreeOnlyForIceDancing{  
	all p:Phase | all i:IceDancing |  not (p in i.containsPhase) =>  not (p in FreeSkatingProgram || p in ShortProgram)
}
fact ShortBeforeFree {
	no f: FreeSkatingProgram | some s: ShortProgram | s in f.next
}
fact SameParticipantsInPhaseAndPerformance{
	all p: FigureSkatingPhase | p.containsPerformance.teams = p.participants
}

fact FreeSkatingParticipantsSubsetOfShortProgram {
	all s: ShortProgram | all f: FreeSkatingProgram | f in s.next => f.participants in s.participants  
}


// FS Score
// Enforces the FigureSkating score constraints
fact allScoresOfIceDancingAreTechOrPres{
	all s:Score | all p:Performance|(p in ShortProgram.containsPerformance || p in FreeSkatingProgram.containsPerformance) && s = p.score
	=> s in FigureSkatingScore
}
fact TechAndPresScoreOnlyForFS{ // inverse of top
	all s:Score | all p:Performance| not (p in ShortProgram.containsPerformance || p in FreeSkatingProgram.containsPerformance) && s = p.score
	=> not( s in FigureSkatingScore)
}
fact TechScorePresScoreMax6{
	all s:FigureSkatingScore | 0 <= s.TechScore && s.TechScore <= 6 && 0 <= s.PresScore && s.PresScore <= 6
}

fact overallFSScore{
	all s:FigureSkatingScore| s.score = plus [s.TechScore ][ s.PresScore]
}

*/

// maybe good idea to make fact TODO
assert SameParticipantsInEventAndPerformance {
	all e: Event | all p: Phase | p in e.containsPhase => ( all t: p.containsPerformance.teams | e in t.participatesIn )  
}


pred show { //EVENT HAS TO BE >1
//	#Event = 3
//	#Location < 5
//	#Time > 1 &&
//	#Performance < 5
//	#Discipline = 1
}

run show for 10

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

// True iff t is among the best teams in phase p. TODO
//pred isAmongBest[t: Team, p: Phase] { ... }

/*
 * Functions

*/

// Returns all the events offered by the discipline d.
fun getEvents[d: Discipline] : set Event { d.containsEvent }  //PMH not tested

// Returns all the teams which participate in the event e.
fun getEventParticipants[e: Event] : set Team {  {t:Team | t in getPerformances[getPhases[e]].teams}} //PMH not tested

// Returns all the phases of the event e.
fun getPhases[e: Event] : set Phase { e.containsPhase } //PMH not tested

// Returns all the performances which take place within the phase p.
fun getPerformances[p: Phase] : set Performance { p.containsPerformance }//PMH not tested

// Returns the set of medals handed out for the event e.
fun getMedals[e: Event] : set Medal { {m:Medal | m.forEvent = e} } //PMH not tested

// Returns the start time of the performance p.
fun getStart[p : Performance] : Time { p.startTime }

// Returns the end time of the performance p.
fun getEnd[p: Performance] : Time { p.stopTime }

// Returns the location of the performance p.
fun getLocation[p: Performance] : Location { p.location } 

// Returns all the teams which paricipate in the performance p.
fun getParticipants[p: Performance] : set Team { p.teams }

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { t.member }

// Returns the team which won the medal m. TODO
//fun getWinner[m: Medal] : Team { ... }

