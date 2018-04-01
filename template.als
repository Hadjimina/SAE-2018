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
	betterEqual: lone Score
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

// Makes chains of Scores per Phase
fact noCircle_Score {
	all s: Score | s not in s.^betterEqual
}
fact onlyOnePredecessor_Score {
	all s:Score | #{ s1:Score | s1.next = s } <= 1
}
fact allScoresInChainInSamePhase {
	all p:Phase | all s:Score | s in p.containsPerformance.score => s.betterEqual in p.containsPerformance.score
}
fact oneLast_Score {
	all p:Phase | one s:Score | s in p.containsPerformance.score && no s.betterEqual
}



// Phases
// Makes chains of phases per Event
fact noCircle_Phases {
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
// Enforces a strictly ordered single chain of Times
fact noCircle_Time{
	no t: Time | t in t.^next
}
fact noTimeLone{
	(one t:Time | no t.next) && (one t1:Time | all t2:Time | (t1 != t2) => t2.next != t1 ) 
}
fact citizenOfRepresentingCountry {
	all a:Athlete | all t: Team | a in t.member => t.represents in a.citizenOf 
}
// TODO: why not working
fact noLocationUsedConcurrently{
//	all disj p0,p1:Performance | p0.location = p1.location => isBefore[p0.stopTime, p1.startTime] 
}
// TODO: why not working
fact noTeamUsedConcurrently {
//	all disj p0,p1:Performance | all t: Team | t in p0.teams && t in p1.teams => isBefore[p0.stopTime, p1.startTime]
}


// Ordering

// No Instance found, Too big of a model or to restrictive?
// Stop time strictly after start time
fact notSameStartAndStopTimeForPerformance {
	 all p:Performance | isBefore[p.startTime, p.stopTime] 
}

// all performances of one phase must end before performances of following phase can start
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
fact noAthleteInTwoCountriesTeams {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && t1.represents != t2.represents
}

// TODO: why not working
fact noAthleteInTwoTeamsPerEvent {
	// There is no athlete for that ( there are two different teams that participate in the same event ) and the athlete is part of both teams
//	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && (t1.participatesIn & t2.participatesIn) != none
}

// Teams
fact noTeamsInDifferentDisciplines {
	all d1, d2: Discipline | all t: Team | teamInDiscipline[t, d1] && teamInDiscipline[t, d2] => d1 = d2
}

fact onlyThreeTeamsPerDisciplinePerCountry {
	all c: Country | all d: Discipline | #{ t: Team | c in t.represents && teamInDiscipline[t, d] } <= 3
}

fact SameParticipantsInEventAndPerformance {
	all e: Event | all p: Phase | p in e.containsPhase => ( all t: p.containsPerformance.teams | e in t.participatesIn )  
}




// For testing
fact testLocationSharing { // SLOWING DOWN ENORMOUSLY // OVERRESTRICTED SOMEWHERE ??
//	some disj p1,p2:Performance | p1.location = p2.location
}
fact testTeamSharing {
//	some disj p1,p2:Performance | p1.teams & p2.teams != none
}
fact testAthleteSharing {
//	some disj t1, t2: Team | t1.member & t2.member != none
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



/* ========================
		Figure Skating 
*/

//Signatures required for the specific part
one sig FigureSkating extends Discipline {}
//{ #FigureSkating <= 1}

one sig IceDancing extends Event {}

abstract sig FigureSkatingPhase extends Phase {
	participants: some Team
}

sig ShortProgram extends FigureSkatingPhase {}
sig FreeSkatingProgram extends FigureSkatingPhase {}

sig Pair extends Team {}

sig FigureSkatingScore extends Score{
	TechScore: one Int,
	PresScore: one Int
}

fact DefinePair {
	all p: Pair | one m:MaleAthlete | one f:FemaleAthlete| m in p.member && f in p.member
}

// Enforces that IceDancing events are only held in the figure skating discipline
fact IceDancingOnlyInFigureSkating{	
	{IceDancing} = FigureSkating.containsEvent
}

// Enforces constraint regarding the free and short program (i.e. phases)
fact TwentyTwoPairsInShortProgram{ 
 	all sp:ShortProgram | #{ t:Team | t in sp.participants} = 5 //change to 22 TODO
}
fact SixteenPairsInFreeSkatingProgram {
	all f: FreeSkatingProgram | # { t: Team | t in f.participants } < 5// change to 16 TODO
}


fact oneShortOneFreePerIceEvent {
	all i: IceDancing | one s: ShortProgram | one f: FreeSkatingProgram | s in i.containsPhase && f in i.containsPhase
}
// only correct because of one sig IceDancing Constraint
fact ShortAndFreeOnlyForIceDancing{  
	all p:Phase | all i:IceDancing |  not (p in i.containsPhase) =>  not (p in FreeSkatingProgram || p in ShortProgram)
}
fact ShortBeforeFree {
	all f: FreeSkatingProgram | all s: ShortProgram | f in s.next
}

fact SameParticipantsInPhaseAndPerformance{
	all p: FigureSkatingPhase | p.containsPerformance.teams = p.participants
}

//implied thorugh best 16
fact FreeSkatingParticipantsSubsetOfShortProgram {
	all s: ShortProgram | all f: FreeSkatingProgram | f in s.next => f.participants in s.participants  
}

fact onlyPairsInIceDancing {
	all t: Team | IceDancing in t.participatesIn <=> t in Pair
}

fact samePhaseSameLocation{
	all p:FigureSkatingPhase | #{p.containsPerformance.location} = 1
}
fact noPhaseAfterFree{ //NEW
	all f:FreeSkatingProgram| no f.next
}
fact onlyFSPhasesForIceDancing{ //NEW
	all i:IceDancing| all p:Phase | p in i.containsPhase =>  p in FigureSkatingPhase 
	
}


// FS Score
// Enforces the FigureSkating score constraints
fact FigureScatingScoreForIceDancing {
	all p:Performance | p in FigureSkatingPhase.containsPerformance <=> p.score in FigureSkatingScore 
}

fact TechScorePresScoreBetween0And6{
	all s:FigureSkatingScore | (0 <= s.TechScore && s.TechScore <= 6) && (0 <= s.PresScore && s.PresScore <= 6)
}

fact RightOrderingScore {
	all disj s1, s2: FigureSkatingScore | s2 in s1.betterEqual => FS_better[s1, s2] || FS_equal[s1, s2]
}

fact someDifferentScores {
	some disj s1, s2: FigureSkatingScore | not FS_equal[s1, s2]
}

fact best16FreeSkating{
	all f: FreeSkatingProgram | all s:ShortProgram |  s.next = f  => get16BestForPhase[s] = {f.containsPerformance.teams} 
}

fact onePerformancePerTeam{ //NEW sensible?
	all p:FigureSkatingPhase| all disj t1, t2:Team| t1 in p.containsPerformance.teams && t2 in p.containsPerformance.teams
	=> performanceForPhaseAndTeam[p,t1] != performanceForPhaseAndTeam[p,t2]
}
fact oneTeamPerFSPerformance{//NEW sensible?
	all p:FigureSkatingPhase | all per:Performance | per in p.containsPerformance => #{per.teams} = 1
}
fact noTeamInTwoPerformancesOfSameFSPhase{
	all t:Team | all disj p1, p2:Performance | all p:FigureSkatingPhase | p1 in p.containsPerformance && p2 in p.containsPerformance 
	=> not (t in  p1.teams && t in  p2.teams)
}

fun get16BestForPhase[p: FigureSkatingPhase]: set Team {//NEW
	{t:Team | t in p.containsPerformance.teams && #{performanceForPhaseAndTeam[p,t].score.^betterEqual} >= 2} //TODO change 2 to 6 (b.c. 22-16 = 6)
}

fun performanceForPhaseAndTeam[p:FigureSkatingPhase, t:Team]:one Performance{//NEW
	{pe:Performance | pe in p.containsPerformance && t in pe.teams}
}


fun FS_fold [s: FigureSkatingScore]: Int { plus [s.TechScore, s.PresScore] }

pred FS_better[s1 , s2 : FigureSkatingScore] { (FS_fold[s1] > FS_fold[s2]) || (FS_fold[s1] = FS_fold[s2] && s1.TechScore > s2.TechScore) }

pred FS_equal [s1, s2: FigureSkatingScore] { FS_fold[s1] = FS_fold[s2] && s1.TechScore = s2.TechScore  }

//fun FS_Phase_Best [i: Int, f: FigureSkatingPhase]: set Team {
//	{ t: f.participants | #{ s: f.containsPerformance.score | FS_better[(t.participatesIn & f.containsPerformance).score, s]  } >= i }
//}
//fun FS_Phase_first_i_Places [i: Int, f: FigureSkatingPhase]: set Team {
//	{ t: f.participants | #{ s: f.containsPerformance.score | FS_better[s, (t.participatesIn & f.containsPerformance).score]  } < i }
//}

//fun FS_Phase_first_i_Teams [i: Int, f: FigureSkatingPhase]: set Team {
//	{ t: f.participants | some t: Int | #{FS_Phase_first_i_Places[t, f] = t t < 16 }}
//}

//check if teams are not in the same phase twice

pred show { //EVENT HAS TO BE >1
//	#Discipline = 2 &&
//	#Event = 2 &&
	//#Athlete > 2// &&
//	#Team < 5 &&
//	#Phase = 1
//	#Location < 5
//	#Time > 1 &&

//	#Performance < 7
//	some p1, p2: Performance | isBefore[p2.startTime, p1.stopTime] && p1.startTime != p2.startTime
	some p:FigureSkatingPhase | #p.containsPerformance > 1
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

