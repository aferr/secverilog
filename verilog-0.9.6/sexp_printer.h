#ifndef SEXP_WRITER
#define SEXP_WRITER

#include <fstream>
#include <functional>
#include <string>
#include <vector>

class Sexception : public std::exception {
public:
  Sexception(const char *message);
  ~Sexception();
  virtual const char *what() const noexcept override;

private:
  static const std::string tag;
  const char *message;
};

class SexpPrinter {
public:
  SexpPrinter(std::ostream &, unsigned int margin, unsigned int tabsize = 2,
              bool allow_naked_atom = false);
  void startList();
  void printAtom(const std::string &atom);
  void endList();
  void addComment(const std::string &comment);
  void lineBreak();
  void startList(const std::string &first);
  void singleton(const std::string &atom);
  void writeRawLine(const std::string &str);
  void inList(const std::string &first,
              const std::function<void(void)> &lambda);

  friend SexpPrinter &operator<<(SexpPrinter &sp, const std::string &atom) {
    sp.printAtom(atom);
    return sp;
  }
  const unsigned int margin;
  const unsigned int tabsize;
  const bool allow_naked_atom;

private:
  enum class State { FRESH, ONE_LINE, MULTI_LINE };
  struct PrintState {
    PrintState(int indent)
        : idnt(indent), st(State::FRESH), acc(), acc_len(0) {}
    unsigned int idnt;
    State st;
    std::vector<std::string> acc;
    unsigned int acc_len;
    void push_to_acc(const std::string &s) {
      acc.push_back(s);
      acc_len += s.size();
      ++acc_len;
      if (st == SexpPrinter::State::FRESH) {
        st = SexpPrinter::State::ONE_LINE;
      }
    }
  };
  std::vector<PrintState> stack;
  std::ostream &o;
};

#endif
