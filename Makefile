all: eval32 eval tests.out

tests.out: eval init.ss tests.ss
	./eval tests.ss > tests.out

eval32.list: eval32
	objdump -C -S eval32 > eval32.list

eval.list: eval
	objdump -C -S eval > eval.list

eval32: eval.cpp
	g++ -m32 -std=c++17 -ggdb3 -o eval32 eval.cpp

eval: eval.cpp
#	g++ -std=c++17 -ggdb3 -o eval eval.cpp
	g++ -DUNWIND -std=c++17 -ggdb3 -O1 -o eval eval.cpp -lunwind

