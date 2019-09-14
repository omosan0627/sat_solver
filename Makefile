num_solver: num_solver.o sat_solver.o
	g++ -Wall -O2 -std=c++0x -o num_solver num_solver.o sat_solver.o

num_solver.o: num_solver.cpp
	g++ -Wall -O2 -std=c++0x -c num_solver.cpp


sat_solver.o: sat_solver.cpp
	g++ -Wall -O2 -std=c++0x -c sat_solver.cpp

sat_solver.o: sat_solver.h

clean:
	rm -f num_solver *.o
