#include "sexp_printer.h"
#include <cstring>
#include <ostream>
#include <sstream>

#include <iostream>

using strvec = std::vector<std::string>;

Sexception::Sexception(const char *m) {
  size_t m_len = strlen(m);
  char *tmp    = (char *)malloc(tag.size() + m_len + 1);
  memcpy(tmp, tag.c_str(), tag.size());
  memcpy(tmp + tag.size(), m, m_len + 1);
  message = tmp;
}

Sexception::~Sexception() { free((char *)message); }

const char *Sexception::what() const noexcept { return message; }

const std::string Sexception::tag = "SexpPrinter: ";

void SexpPrinter::startList() {
  unsigned int idnt = 0;
  if (!stack.empty()) {
    switch (stack.back().st) {
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
  stack.emplace_back(idnt);
}

void SexpPrinter::printAtom(const std::string &atom) {
  if (stack.empty()) {
    if (allow_naked_atom) {
      o << atom;
      return;
    }
    throw Sexception("cannot print naked atom!");
  }
  if (atom.empty())
    return;
  auto &state = stack.back();
  switch (state.st) {
  case SexpPrinter::State::FRESH:
    state.push_to_acc(atom);
    break;
  case SexpPrinter::State::ONE_LINE:
    state.push_to_acc(atom);
    if (state.acc_len + state.idnt > margin) {
      int delta = -1;
      for (auto &s : stack) {
        if (delta < 0) {
          if (s.st == SexpPrinter::State::ONE_LINE) {
            s.st = SexpPrinter::State::MULTI_LINE;
            std::string indent(s.idnt, ' ');
            s.idnt += tabsize;
            std::string more_indent(tabsize, ' ');
            for (auto &str : s.acc) {
              if (&str == &s.acc.front())
                o << (&s == &stack.front() ? "" : "\n") << indent << "(" << str;
              else
                o << std::endl << indent << more_indent << str;
            }
            delta = s.acc_len;
          }
        } else {
          s.idnt -= delta;
        }
      }
    }
    break;
  case SexpPrinter::State::MULTI_LINE:
    std::string indent(state.idnt, ' ');
    o << std::endl << indent << atom;
  }
}
void SexpPrinter::endList() {
  if (stack.empty())
    throw Sexception("mismatched delimiters");
  auto &state = stack.back();
  switch (state.st) {
  case SexpPrinter::State::FRESH:
  case SexpPrinter::State::ONE_LINE:
    if (stack.size() == 1) {
      o << "(";
      for (const auto &at : state.acc) {
        o << at;
        if (&at != &state.acc.back())
          o << " ";
      }
      o << ")";
    } else {
      std::stringstream str;
      str << "(";
      for (const auto &at : state.acc) {
        str << at;
        if (&at != &state.acc.back())
          str << " ";
      }
      str << ")";
      auto &prev = *std::prev(std::prev(stack.end()));
      if (prev.st == SexpPrinter::State::MULTI_LINE)
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
  if (stack.empty())
    o << std::endl;
}

void SexpPrinter::addComment(const std::string &comment) {
  if (!stack.empty())
    throw Sexception("cannot add comment inside of S-expression");
  o << ";; " << comment << std::endl;
}

void SexpPrinter::lineBreak() {
  if (!stack.empty())
    throw Sexception("cannot add line break inside of S-expression");
  o << std::endl;
}

void SexpPrinter::startList(const std::string &first) {
  startList();
  printAtom(first);
}

SexpPrinter::SexpPrinter(std::ostream &os, unsigned int m, unsigned int ts,
                         bool alw)
    : margin(m), tabsize(ts), allow_naked_atom(alw), stack(), o(os) {}

void SexpPrinter::singleton(const std::string &atom) {
  startList(atom);
  endList();
}

void SexpPrinter::writeRawLine(const std::string &str) {
  if (!stack.empty())
    throw Sexception("cannot write raw line inside of S-expression");
  o << str << std::endl;
}

void SexpPrinter::inList(const std::string &first,
                         const std::function<void()> &lambda) {
  startList(first);
  lambda();
  endList();
}
