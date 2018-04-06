sig Discipline { 
	containsEvent: some Event //not shared
}

sig Event {
	containsPhase: some Phase, // not shared
}

sig Phase { 
	next: lone Phase, 
	containsPerformance: some Performance // not shared
}


sig Performance {
	location: one Location, // can be shared
	startTime: one Time, // can be shared
	stopTime: one Time, // "
	score: one Score, // not shared
	teams: some Team

} 

sig Score { 
	betterEqual: lone Score
}

sig Location { }

sig Time {
	next: lone Time 
}

sig Team { 
	participatesIn: some Event,
	represents: one Country,
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

// COMPOSITION
/**/
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
fact minOnePerformancePerLocation {
	all l:Location | some p:Performance | l in p.location
}
fact noLoseTime {
	all t:Time | some p:Performance | t in p.stopTime || t in p.startTime
}
fact minOnePerformancePerTeam {
	all t: Team | some p: Performance | t in p.teams
}


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
fact noLocationUsedConcurrently{
	all disj p0,p1:Performance | {p0.location} = {p1.location} && isBefore[p0.startTime, p1.startTime] => isBefore[p0.stopTime, p1.startTime]
}
fact noTeamUsedConcurrently {
	all disj p0,p1:Performance | all t: Team | t in p0.teams && t in p1.teams => isBefore[p0.stopTime, p1.startTime]
}

// Ordering
// Stop time strictly after start time
fact notSameStartAndStopTimeForPerformance {
	all p:Performance| p.stopTime in p.startTime.^next
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

//Athletes
fact noAthleteInTwoCountriesTeams {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && t1.represents != t2.represents
}

fact noAthleteInTwoTeamsPerEvent {
	no a:Athlete | some disj t1, t2:Team | a in t1.member && a in t2.member && #{t1.participatesIn & t2.participatesIn} > 0
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



/* ========================
		Figure Skating 
*/


//Signatures required for the specific part
one sig FigureSkating extends Discipline {}

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

//Enforces figures skating performance constraints
fact onePerformancePerTeam{
	all p:FigureSkatingPhase| all disj t1, t2:Team| t1 in p.containsPerformance.teams && t2 in p.containsPerformance.teams
	=> performanceForPhaseAndTeam[p,t1] != performanceForPhaseAndTeam[p,t2]
}
fact oneTeamPerFSPerformance{
	all p:FigureSkatingPhase | all per:Performance | per in p.containsPerformance => #{per.teams} = 1
}


// Enforces that IceDancing events are only held in the figure skating discipline
fact IceDancingOnlyInFigureSkating{	//CONFLICt
	{IceDancing} = FigureSkating.containsEvent
}

// Enforces constraint regarding the free and short program (i.e. phases)
fact TwentyTwoPairsInShortProgram{ 
 	all sp:ShortProgram | #{ t:Team | t in sp.participants} = 5
}
fact SixteenPairsInFreeSkatingProgram {
	all f: FreeSkatingProgram | # { t: Team | t in f.participants } < 5
}
fact oneShortOneFreePerIceEvent { 
	IceDancing .containsPhase = ShortProgram + FreeSkatingProgram
}
// only correct because of one sig IceDancing Constraint
fact ShortAndFreeOnlyForIceDancing{  
	all p:Phase | all i:IceDancing |  not (p in i.containsPhase) =>  not (p in FreeSkatingProgram || p in ShortProgram)
}
fact ShortBeforeFree { 
	all f: FreeSkatingProgram | all s: ShortProgram | f in s.next
}

fact SameParticipantsInPhaseAndPerformance{
	all p: FigureSkatingPhase | p.containsPerformance.teams in p.participants
}

//implied thorugh best 16
fact FreeSkatingParticipantsSubsetOfShortProgram {
	all p:Pair | p in FreeSkatingProgram.containsPerformance.teams => p in ShortProgram.containsPerformance.teams
}

fact onlyPairsInIceDancing {
 	all t:Team | t in IceDancing.containsPhase.containsPerformance.teams <=> t in  Pair 	
}

fact samePhaseSameLocation{
	all p:FigureSkatingPhase | #{p.containsPerformance.location} = 1
}
fact noPhaseAfterFree{
	all f:FreeSkatingProgram| no f.next
}

fact onlyFSPhasesForIceDancing{
	all i:IceDancing| all p:Phase | p in i.containsPhase =>  p in FigureSkatingPhase 
}


// FS Score
// Enforces the FigureSkating score constraints
fact FigureScatingScoreForIceDancing {
	{all p:Performance | p in FigureSkatingPhase.containsPerformance <=> p.score in FigureSkatingScore} && { FigureSkatingPhase.containsPerformance.score = FigureSkatingScore }
}
fact TechScorePresScoreBetween0And6{
	all s:FigureSkatingScore | (0 <= s.TechScore && s.TechScore <= 6) && (0 <= s.PresScore && s.PresScore <= 6)
}

fact RightOrderingScore {
	all disj s1, s2: FigureSkatingScore | s2 in s1.betterEqual => FS_better[s1, s2] || FS_equal[s1, s2]
}

fact someDifferentScores {
	all disj s1, s2: FigureSkatingScore | not FS_equal[s1, s2]
}

fact best16FreeSkating{ //NO INSTANCE
//	get16BestForPhase[ShortProgram] = {FreeSkatingProgram.containsPerformance.teams} 
}

fact noTeamInTwoPerformancesOfSameFSPhase{
	all t:Team | all disj p1, p2:Performance | all p:FigureSkatingPhase | p1 in p.containsPerformance && p2 in p.containsPerformance 
	=> not (t in  p1.teams && t in  p2.teams)
}

fun get16BestForPhase[p: FigureSkatingPhase]: set Team {
	{t:Team | t in p.containsPerformance.teams && #{performanceForPhaseAndTeam[p,t].score.^betterEqual} >= 3}
	//{t:Team | t in IceDancing.containsPhase.containsPerformance.teams && }
}

fun performanceForPhaseAndTeam[p:FigureSkatingPhase, t:Team]:one Performance{
	{pe:Performance | pe in p.containsPerformance && t in pe.teams}
}

fun FS_fold [s: FigureSkatingScore]: Int { plus [s.TechScore, s.PresScore] }

pred FS_better[s1 , s2 : FigureSkatingScore] { (FS_fold[s1] > FS_fold[s2]) || (FS_fold[s1] = FS_fold[s2] && s1.TechScore > s2.TechScore) }

pred FS_equal [s1, s2: FigureSkatingScore] { FS_fold[s1] = FS_fold[s2] && s1.TechScore = s2.TechScore  }

fact reverseOrderInFreeAsInShort{ 
	all s:ShortProgram | all f:FreeSkatingProgram| all disj t1,t2:Team | s.next = f && t1 in s.containsPerformance.teams && t1 in f.containsPerformance.teams
	&& t2 in s.containsPerformance.teams && t2 in f.containsPerformance.teams && isBefore[performanceForPhaseAndTeam[s,t1].startTime,performanceForPhaseAndTeam[s,t2].startTime]
	=> isBefore[performanceForPhaseAndTeam[f,t2].startTime,performanceForPhaseAndTeam[f,t1].startTime]
}


fun FS_Phase_first_i_Places [i: Int, f: FigureSkatingPhase]: set Team {
	{ t: f.participants | #{ s: f.containsPerformance.score | FS_better[s, performanceForPhaseAndTeam[f, t].score]  } < i }
}
fun GoldCandidates[f: FigureSkatingPhase]: set Team {
	FS_Phase_first_i_Places[1, f]
}
fun SilverCandidates[f: FigureSkatingPhase]: set Team {
	FS_Phase_first_i_Places[2, f] - GoldCandidates[f]
}
fun BronzeCandidates[f: FigureSkatingPhase]: set Team {
	FS_Phase_first_i_Places[3, f] - GoldCandidates[f] - SilverCandidates[f]
}


pred FS_case1_Medals[] {
	#{ m: GoldMedal | IceDancing in m.forEvent} = 1 &&
	#{ m: SilverMedal | IceDancing in m.forEvent} = 1 &&
	#{ m: BronzeMedal | IceDancing in m.forEvent} >= 1
}
pred FS_case2_Medals[] {
	#{ m: GoldMedal | IceDancing in m.forEvent} = 1 &&
	#{ m: SilverMedal | IceDancing in m.forEvent} >= 2 &&
	#{ m: BronzeMedal | IceDancing in m.forEvent} = 0
}
pred FS_case3_Medals[] {
	#{ m: GoldMedal | IceDancing in m.forEvent} = 2 &&
	#{ m: SilverMedal | IceDancing in m.forEvent} = 0 &&
	#{ m: BronzeMedal | IceDancing in m.forEvent} >= 1
}
pred FS_case4_Medals[] {
	#{ m: GoldMedal | IceDancing in m.forEvent} >= 3 &&
	#{ m: SilverMedal | IceDancing in m.forEvent} = 0 &&
	#{ m: BronzeMedal | IceDancing in m.forEvent} = 0
}



fact MedalsForSkating {
	all e: IceDancing | 
	//Case 1
	(FS_case1_Medals[] => (
			(all m:GoldMedal | IceDancing in m.forEvent <=> m.forTeam in GoldCandidates[FreeSkatingProgram]) &&
			(all m:SilverMedal | IceDancing in m.forEvent <=> m.forTeam in SilverCandidates[FreeSkatingProgram]) &&
			(all m:BronzeMedal | IceDancing in m.forEvent <=> m.forTeam in BronzeCandidates[FreeSkatingProgram])
	))
	&&
	//Case 2 
	(FS_case2_Medals[] => (
			(all m:GoldMedal | e in m.forEvent <=> m.forTeam in GoldCandidates[FreeSkatingProgram]) &&
			(all m:SilverMedal | e in m.forEvent <=> m.forTeam in SilverCandidates[FreeSkatingProgram]) &&
			(no m:BronzeMedal | e in m.forEvent)
	))
	&&
	//Case 3
	(FS_case3_Medals[] => (
			(all m:GoldMedal | e in m.forEvent <=> m.forTeam in GoldCandidates[FreeSkatingProgram]) &&
			(no m:SilverMedal | e in m.forEvent) &&
			(all m:BronzeMedal | e in m.forEvent <=> m.forTeam in SilverCandidates[FreeSkatingProgram])
	))
	&&
	//Case 4
	(FS_case4_Medals[] => (
			(all m:GoldMedal | e in m.forEvent <=> m.forTeam in GoldCandidates[FreeSkatingProgram]) &&
			(no m:SilverMedal | e in m.forEvent) &&
			(no m:BronzeMedal | e in m.forEvent)
	))	
}




//GENERAL PART
pred static_instance_1{ // done
	#Performance = 7 &&
	#Location = 2 &&
	#Time = 4
}
pred static_instance_2 { //done
	some a:Athlete | some d1: Discipline | some p1, p2: Performance | 
		p1 in d1.containsEvent.containsPhase.containsPerformance &&
		p2 not in d1.containsEvent.containsPhase.containsPerformance 
		&& a in p1.teams.member 
		&& a in p2.teams.member
		&& p2.startTime = p1.stopTime.next 
}
pred static_instance_3{ //done
	some c:Country | no t:Team | c in t.represents
}

pred static_instance_4{ //done
	some a:Athlete| some disj g1,g2:GoldMedal | a in g1.forTeam.member && a in g2.forTeam.member && {d:Discipline | g1.forEvent in d.containsEvent} = {d:Discipline | g2.forEvent in d.containsEvent}
}

//SPECIFIC PART
pred static_instance_5{
	one t:Team| one g:GoldMedal |  not isAmongBest[t, ShortProgram] && IceDancing in g.forEvent && t in g.forTeam
}

pred static_instance_6{ 
	#{ m: GoldMedal | IceDancing in m.forEvent} = 1 &&
	#{ m: BronzeMedal | IceDancing in m.forEvent} >= 1
}

pred show{
	one p:Pair | p in FreeSkatingProgram.containsPerformance.teams && p in ShortProgram.containsPerformance.teams && #{ShortProgram.containsPerformance.teams}>=3 &&#{FreeSkatingProgram.containsPerformance.teams}>=1
}

fact winnerWinnerChickenDinner{
	all t:Team| all g:GoldMedal | isAmongBest[t,FreeSkatingProgram] && IceDancing in g.forEvent  <=> t in g.forTeam && IceDancing in g.forEvent
}

run  static_instance_5 for 6

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
pred isAmongBest[t: Team, p: Phase] { 
	#{s:FigureSkatingScore | s in p.containsPerformance.score && s != performanceForPhaseAndTeam[p,t].score && FS_better[s,performanceForPhaseAndTeam[p,t].score]} = 0
} 

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

// Returns the team which won the medal m. 
fun getWinner[m: Medal] : Team { m.forTeam }//PMH not tested

