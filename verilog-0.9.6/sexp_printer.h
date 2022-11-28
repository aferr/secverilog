#ifndef SEXP_WRITER
#define SEXP_WRITER

#include <string>
#include <fstream>
#include <sstream>
#include <vector>
#include <stack>
#include <list>

#include <iostream>

class SexpPrinter
{
 public:
  SexpPrinter(std::ostream &, unsigned int margin, unsigned int tabsize = 2);
  ~SexpPrinter();
  void startList();
  void printAtom(const std::string &atom);
  void endList();
  void addComment(const std::string &comment);
  void lineBreak();
  void startList(const std::string &first);
  void singleton(const std::string &atom);
  void writeRawLine(const std::string &str);

  friend SexpPrinter&operator<<(SexpPrinter &sp, const std::string &atom)
  {
    sp.printAtom(atom);
    return sp;
  }
  const unsigned int margin;
  const unsigned int tabsize;
 private:
  enum class State
  {
    FRESH, ONE_LINE, MULTI_LINE
  };
  struct PrintState
  {
    unsigned int idnt;
    State st;
    std::vector<std::string> acc;
    unsigned int acc_len;
    void push_to_acc(const std::string &s)
    {
      acc.push_back(s);
      acc_len += s.size();
      ++acc_len;
      if(st == SexpPrinter::State::FRESH)
	{
	  st = SexpPrinter::State::ONE_LINE;
	}
    }
  };
  std::vector<PrintState> stack;
  std::ostream &o;
  //std::ofstream logger;
};

#endif
