/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */

sig Athlete { ... }

sig Discipline { ... }

sig Event { ... }

sig Location { ... }

sig Medal { ... }

sig Performance { ... } 

sig Phase { ... }

sig Team { ... }

sig Time { ... }

/*
 * Predicates
 */

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
 */

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
