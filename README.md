# ICKakuro

Kakuro deductive resolution in CLIPS for Knowledge Engineering in [MULCIA](https://www.informatica.us.es/index.php/masteres/mulcia) at [University of Seville](http://www.us.es/).

Kakuro is one of the logical pastimes popularized by the Japanese magazine Nikoli. Along with Sudoku is one of the most widespread worldwide. The aim of the game is to place numbers from 1 to 9 in the boxes of a predetermined board so that the sum of the numbers in the adjacent boxes of each row and column of the board is indicated in the margins thereof, with the additional restriction that repeated numbers can not appear in contiguous boxes.

An example of Kakuro board is as given below:

[![1](https://www.cs.us.es/cursos/ic/trabajo/kakuro.png)]

The solution of the example is as given below:

[![2](https://www.cs.us.es/cursos/ic/trabajo/kakuro-resuelto.png)]

We will say that Kakuro is well posed if it has a unique solution.

The aim of this work is to implement a CLIPS software that it can solve any Kakuro using deductively. It is to get the value of the boxes of the board using rules, which they analyze the possible values of the related boxes.

It can be done using rules that determine the value of a cell, or that eliminate possible values of its range.
