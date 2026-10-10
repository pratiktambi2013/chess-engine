CXX ?= g++
CXXFLAGS ?= -O3 -DNDEBUG -std=c++17 -Wall -Wextra -Wpedantic
LDFLAGS ?= -pthread
TARGET := mitra
SOURCE := src/engine.cpp

.PHONY: all clean test bench

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) $(SOURCE) -o $@ $(LDFLAGS)

test: $(TARGET)
	./$(TARGET) --selftest

bench: $(TARGET)
	./$(TARGET) --bench 6

clean:
	rm -f $(TARGET)
