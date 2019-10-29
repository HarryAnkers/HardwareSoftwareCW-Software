theory HSV_chapter5 imports Main begin

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

text \<open>A function that optimises a circuit by removing pairs of consecutive NOT gates\<close>

fun opt_NOT where
  "opt_NOT (NOT (NOT c)) = opt_NOT c"
| "opt_NOT (NOT c) = NOT (opt_NOT c)"
| "opt_NOT (AND c1 c2) = AND (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT (OR c1 c2) = OR (opt_NOT c1) (opt_NOT c2)"
| "opt_NOT TRUE = TRUE"
| "opt_NOT FALSE = FALSE"
| "opt_NOT (INPUT i) = INPUT i"

text \<open>Trying out the optimiser\<close>

value "circuit1"
value "opt_NOT circuit1"
value "circuit2"
value "opt_NOT circuit2"
value "circuit3"
value "opt_NOT circuit3"
value "circuit4"
value "opt_NOT circuit4"

text \<open>The following non-theorem is easily contradicted.\<close>

theorem "opt_NOT c = c" 
  oops

text \<open>The following theorem says that the optimiser is sound.\<close>

theorem opt_NOT_is_sound: "simulate (opt_NOT c) \<rho> = simulate c \<rho>"
  by (induct rule: opt_NOT.induct, auto)

text \<open>The following function calculates the area of a circuit (i.e. number of gates).\<close>

fun area :: "circuit \<Rightarrow> nat" where
  "area (NOT c) = 1 + area c"
| "area (AND c1 c2) = 1 + area c1 + area c2"
| "area (OR c1 c2) = 1 + area c1 + area c2"
| "area _ = 0"

end
