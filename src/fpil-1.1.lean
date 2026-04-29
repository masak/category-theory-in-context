#eval 1 + 2             -- 3

#eval 1 + 2 * 5         -- 11, rather than 15

-- rather than writing `String.append("Hello, ", "Lean!")`
#eval String.append "Hello, " "Lean!"

-- parentheses are required in
#eval String.append "great " (String.append "oak " "tree")
-- because otherwise the second `String.append` would be
-- interpreted as an argument to the first

-- this would lead to an error message:
-- #eval String.append "it is "
--
-- expression
--   String.append "it is "
-- has type
--   String → String
-- but instance
--   Lean.MetaEval (String → String)
-- failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.MetaEval` class

-- # Exercises

-- What are the values of the following expressions? Work them out by hand, then enter them into Lean to check your work.

-- Q: 42 + 19
-- A: 61
#eval 42 + 19

-- Q: String.append "A" (String.append "B" "C")
-- A: "ABC"
#eval String.append "A" (String.append "B" "C")

-- Q: String.append (String.append "A" "B") "C"
-- A: "ABC" (associative law on display here"
#eval String.append (String.append "A" "B") "C"

-- Q: if 3 == 3 then 5 else 7
-- A: 5
#eval if 3 == 3 then 5 else 7

-- Q: if 3 == 4 then "equal" else "not equal"
-- A: "not equal"
#eval if 3 == 4 then "equal" else "not equal"
