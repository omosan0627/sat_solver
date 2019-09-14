sat: sat.o sat_solver.o
	g++ -Wall -O2 -std=c++0x -o sat sat.o sat_solver.o

sat.o: sat.cpp
	g++ -Wall -O2 -std=c++0x -c sat.cpp


sat_solver.o: sat_solver.cpp
	g++ -Wall -O2 -std=c++0x -c sat_solver.cpp

sat_solver.o: sat_solver.h

clean:
	rm -f sat *.o
