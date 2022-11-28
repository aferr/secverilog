#include "sexp_printer.h"
#include <ostream>
#include <type_traits>


using strvec = std::vector<std::string>;

void SexpPrinter::startList()
{
  //logger << "printer.startList();\n";
  std::cout << "starting list" << std::endl;
  unsigned int idnt = 0;
  if(!stack.empty())
    {
      switch(stack.back().st)
	{
	case SexpPrinter::State::MULTI_LINE:
	  idnt = stack.back().idnt;
	  break;
	case SexpPrinter::State::ONE_LINE:
	  idnt = stack.back().idnt + stack.back().acc_len + tabsize;
	  break;
	case SexpPrinter::State::FRESH:
	  idnt = stack.back().idnt + tabsize;
	}
    }
  SexpPrinter::PrintState st{idnt, SexpPrinter::State::FRESH, strvec{}, 0};
  std::cout << "created state" << std::endl;
  stack.push_back(st);
  std::cout << "started list" << std::endl;
}


void SexpPrinter::printAtom(const std::string &atom)
{
  std::cout << "printing atom: " << atom << std::endl;
  //logger << "printer.printAtom(\"" << atom << "\");\n";
  if(atom.empty())
    return;
  auto &state = stack.back();
  switch(state.st)
    {
    case SexpPrinter::State::FRESH:
      state.push_to_acc(atom);
      break;
    case SexpPrinter::State::ONE_LINE:
      state.push_to_acc(atom);
      if(state.acc_len + state.idnt > margin)
	{
	  int delta = -1;
	  for(auto &s : stack)
	    {
	      if(delta < 0)
		{
		  if(s.st == SexpPrinter::State::ONE_LINE)
		    {
		      //std::cout << "changing to multiline" << std::endl;
		      s.st = SexpPrinter::State::MULTI_LINE;
		      //s.idnt -= s.acc.front().size();
		      std::string indent(s.idnt, ' ');
		      s.idnt += tabsize;
		      std::string more_indent(tabsize, ' ');
		      for(auto &str : s.acc)
			{
			  //std::cout << "printing: " << str << std::endl;
			  if(&str == &s.acc.front())
			    o << (&s == &stack.front() ? "" : "\n") << indent << "(" << str;
			  else
			    o << std::endl << indent << more_indent << str;
			}
		      delta = s.acc_len;
		    }
		} else
		{
		  s.idnt -= delta;
		}
	    }
        }
      break;
    case SexpPrinter::State::MULTI_LINE:
      //std::cout << "multiline print: " << atom << std::endl;
      std::string indent(state.idnt, ' ');
      o << std::endl << indent << atom;
    }
}
void SexpPrinter::endList()
{
  //logger << "printer.endList();\n";
  if(stack.empty())
    throw("mismatched delimiters");
  auto &state = stack.back();
  switch(state.st)
    {
    case SexpPrinter::State::FRESH:
    case SexpPrinter::State::ONE_LINE:
      if(stack.size() == 1)
	{
	  o << "(";
	  for(const auto &at : state.acc)
	    {
	      o << at;
	      if(&at != &state.acc.back())
		o << " ";
	    }
	  o << ")";
	} else
	{
	  std::stringstream str;
	  str << "(";
	  for(const auto &at : state.acc)
	    {
	      str << at;
	      if(&at != &state.acc.back())
		str << " ";
	    }
	  str << ")";
	  auto &prev = *std::prev(std::prev(stack.end()));
	  if(prev.st == SexpPrinter::State::MULTI_LINE)
	    o << std::endl << std::string(prev.idnt, ' ') << str.str();
	  else
	    prev.push_to_acc(str.str());
	}
      break;
    case SexpPrinter::State::MULTI_LINE:
      o << ")";
      break;
    }
  stack.pop_back();
  if(stack.empty())
    o << std::endl;
}

void SexpPrinter::addComment(const std::string &comment)
{
  //logger << "printer.addComment(\"" << comment << "\");\n";
  if(!stack.empty())
    throw("cannot add comment inside of S-expression");
  o << ";; " << comment << std::endl;
}

void SexpPrinter::lineBreak()
{
  //logger << "printer.lineBreak();\n";
  if(!stack.empty())
    throw("cannot add line break inside of S-expression");
  o << std::endl;
}


void SexpPrinter::startList(const std::string &first)
{
  startList();
  printAtom(first);
}

SexpPrinter::SexpPrinter(std::ostream &os, unsigned int m, unsigned int ts)
    : margin(m), tabsize(ts), stack(), o(os) {
  //logger.open("sexp_log.cc");
}

void SexpPrinter::singleton(const std::string &atom)
{
  startList(atom);
  endList();
}

void SexpPrinter::writeRawLine(const std::string &str)
{
  if(!stack.empty())
    throw("cannot write raw line inside of S-expression");
  o << str << std::endl;
}


SexpPrinter::~SexpPrinter()
{
  //logger.close();
  std::cout << "destroying with stack size: " << stack.size() << std::endl;
}
