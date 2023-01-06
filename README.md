# CS143 Compiler - Assignment (WIP)
This is my answer to the public course assignments whose purpose is to design a compiler for COOL language. Resources can be found on both course official website and edx; a combination is preferred.

The course itself contains more theories (especially fundamental theories which are implemented by mature tools like flex & bison) than the assignments. Merely completing assignments may be insufficient, try quizzes (found on edx) and tests (found on official website) to examine your degree of mastery.

* PA1
  * not graded, passed simple manually configured tests
  * write a simple COOL program (roughly 200 lines), to get familiar with syntax

* PA2 - lexical analysis
  * `You got a score of 63 out of 63.`
  * see `cool.flex`

* PA3 - parsing
  * `You got a score of 70 out of 70.`
  * see `cool.y`
  * do not use `yyerrok` (i.e. error recovery) QAQ; to conform to the grading script, just keep error handling simple

