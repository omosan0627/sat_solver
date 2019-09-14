num_solver: num_solver.o sat_solver.o
	g++ -Wall -O3 -mtune=native -march=native -std=c++0x -o num_solver num_solver.o sat_solver.o

sat: sat.o sat_solver.o
	g++ -Wall -O3 -mtune=native -march=native -std=c++0x -o sat sat.o sat_solver.o

sat.o: sat.cpp
	g++ -Wall -O3 -mtune=native -march=native -std=c++0x -c sat.cpp

num_solver.o: num_solver.cpp
	g++ -Wall -O3 -mtune=native -march=native -std=c++0x -c num_solver.cpp


sat_solver.o: sat_solver.cpp
	g++ -Wall -O3 -mtune=native -march=native -std=c++0x -c sat_solver.cpp

sat_solver.o: sat_solver.h

clean:
	rm -f num_solver sat *.o
