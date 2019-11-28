theory HSV_CW_4_11 imports Main begin

text \<open>Defining a data structure to represent fan-out-free circuits with numbered inputs\<close>

datatype "circuit" = 
  NOT "circuit"
| AND "circuit" "circuit"
| OR "circuit" "circuit"
| TRUE
| FALSE
| INPUT "int"

text \<open>A few example circuits\<close>

definition "circuit1 == AND (INPUT 1) (INPUT 2)"
definition "circuit2 == OR (NOT circuit1) FALSE"
definition "circuit3 == NOT (NOT circuit2)"
definition "circuit4 == AND circuit3 (INPUT 3)"

text \<open>Simulates a circuit given a valuation for each input wire\<close>

fun simulate where
  "simulate (AND c1 c2) \<rho> = ((simulate c1 \<rho>) \<and> (simulate c2 \<rho>))"
| "simulate (OR c1 c2) \<rho> = ((simulate c1 \<rho>) \<or> (simulate c2 \<rho>))"
| "simulate (NOT c) \<rho> = (\<not> (simulate c \<rho>))"
| "simulate TRUE \<rho> = True"
| "simulate FALSE \<rho> = False"
| "simulate (INPUT i) \<rho> = \<rho> i"

text \<open>A few example valuations\<close>

definition "\<rho>0 == \<lambda>_. True"
definition "\<rho>1 == \<rho>0(1 := True, 2 := False, 3 := True)"
definition "\<rho>2 == \<rho>0(1 := True, 2 := True, 3 := True)"

text \<open>Trying out the simulator\<close>

value "simulate circuit1 \<rho>1"
value "simulate circuit2 \<rho>1"
value "simulate circuit3 \<rho>1"
value "simulate circuit4 \<rho>1"
value "simulate circuit1 \<rho>2"
value "simulate circuit2 \<rho>2"
value "simulate circuit3 \<rho>2"
value "simulate circuit4 \<rho>2"

text \<open>A function that optimises a circuit by demorgans theorem\<close>

fun optDM where
  "optDM (AND (NOT c1) (NOT c2)) = NOT (OR (optDM c1) (optDM c2))"
| "optDM (OR (NOT c1) (NOT c2)) = NOT (AND (optDM c1) (optDM c2))"
| "optDM (NOT c) = NOT (optDM c)"
| "optDM (AND c1 c2) = AND (optDM c1) (optDM c2)"
| "optDM (OR c1 c2) = OR (optDM c1) (optDM c2)"
| "optDM TRUE = TRUE"
| "optDM FALSE = FALSE"
| "optDM (INPUT i) = INPUT i"

text \<open>A function that optimises a circuit by removing pairs of consecutive NOT gates\<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open>A function that checks if the optimisation happened\<close>

fun NOT_check where
  "NOT_check (NOT (NOT c)) = True"
| "NOT_check (NOT c) = NOT_check c"
| "NOT_check (AND c1 c2) = ((NOT_check c1) \<or> (NOT_check c2))"
| "NOT_check (OR c1 c2) = ((NOT_check c1) \<or> (NOT_check c2))"
| "NOT_check _ = False"

text \<open>A function to calculate the longest path in a circuit\<close>

fun delay where
  "delay (NOT c) = 1 + NOT_check c"
| "delay (AND c1 c2) = 1 + ((delay c1)>(delay c2)) ? (delay c1) : (delay c2)"
| "delay (OR c1 c2) = 1 + ((delay c1)>(delay c2)) ? (delay c1) : (delay c2)"
| "delay _ = 1"

text \<open>A function to calculate the area of a circuit\<close>

fun area where
  "area (NOT c) = 1 +  area(c)"
| "area (AND c1 c2) = 1 + area(c1) + area(c2)"
| "area (OR c1 c2) =1 + area(c1) + area(c2)"
| "area _ = 0"

text \<open>A function to perform constant folding\<close>

fun opt_FOLDING where
  "opt_FOLDING (NOT TRUE) = FALSE"
| "opt_FOLDING (NOT FALSE) = TRUE"
| "opt_FOLDING (NOT c) = NOT (opt_FOLDING c)"
| "opt_FOLDING (AND TRUE c) = (opt_NOT c)"
| "opt_FOLDING (AND FALSE c) = FALSE"
| "opt_FOLDING (AND c TRUE) = (opt_NOT c)"
| "opt_FOLDING (AND c FALSE) = FALSE"
| "opt_FOLDING (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_FOLDING (OR TRUE c) = TRUE"
| "opt_FOLDING (OR FALSE c) = (opt_NOT c)"
| "opt_FOLDING (OR c TRUE) = TRUE"
| "opt_FOLDING (OR c FALSE) = (opt_NOT c)"
| "opt_FOLDING (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_FOLDING TRUE = TRUE"
| "opt_FOLDING FALSE = FALSE"
| "opt_FOLDING (INPUT i) = INPUT i"

fun contains_input where
  "contains_input (NOT c) = contains_input c"
| "contains_input (AND c1 c2) = ((contains_input c1) \<and> (contains_input c2))"
| "contains_input (OR c1 c2) = ((contains_input c1) \<and> (contains_input c2))"
| "contains_input TRUE = True"
| "contains_input FALSE = True"
| "contains_input (INPUT i) = False"

text \<open>Simulating and checking\<close>

value "circuit1"
value "optDM circuit1"
value "opt_NOT circuit1"
value "NOT_check circuit1"
value "circuit2"
value "optDM circuit2"
value "opt_NOT circuit2"
value "NOT_check circuit2"
value "circuit3"
value "optDM circuit3"
value "opt_NOT circuit3"
value "NOT_check circuit3"
value "circuit4"
value "optDM circuit4"
value "opt_NOT circuit4"
value "NOT_check circuit4"

text \<open>The following theorem says that the not optimiser is sound.\<close>

theorem opt_NOT_is_sound: "simulate (opt_NOT c) \<rho> = simulate c \<rho>"
  apply (induct rule:opt_NOT.induct)
  apply auto
  done

text \<open>The following theorem says that the demorgan optimiser is sound.\<close>

theorem optDM_is_sound: "simulate (optDM c) \<rho> = simulate c \<rho>"
  apply (induct rule:optDM.induct)
  apply auto
  done

text \<open>The following theorem says that the demorgan and not can be successive\<close>

theorem optDM_opt_NOT_successive: "(simulate (opt_NOT (optDM c)) \<rho> = simulate c \<rho>) \<and>
                         (simulate (optDM (opt_NOT c)) \<rho> = simulate c \<rho>)"
  by (simp add: optDM_is_sound opt_NOT_is_sound) 
  done

text \<open>Area never increases\<close>

theorem "(area (optDM (c)) \<le> area (c)) \<and>
         (area (opt_NOT (c)) \<le> area (c))" 
  by try

text \<open>Proves Opt DM is not idempotent (counter example: and(and(not(i0),not(i1)),not(i3)) )\<close>

theorem "optDM(c) = optDM(optDM(c))" 
  oops

text \<open>The following theorem says that 2 not opts doesn't change anything\<close>

theorem consecutive_not: "opt_NOT(c) = opt_NOT(opt_NOT(c))" 
  apply try
  done

text \<open>The following theorem says if there is a not opt then opt not changes C\<close>

theorem opt_not_changes: "if NOT_check(c) then opt_NOT(c) \<noteq> c else opt_NOT(c) = c" 
  apply try
  done

text \<open>The following theorem says if contains no input then it must be TRUE or FALSE\<close>

theorem folding_no_input: "if contains_no_input(c) then ((opt_FOLDING(c) = TRUE) \<or>
                          (opt_FOLDING(c) = FALSE))" 
  apply try
  done


end
