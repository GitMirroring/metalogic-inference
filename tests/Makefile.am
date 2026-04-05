


dist_noinst_HEADERS = mli-test \
  issue-meta-0.mli issue-meta-0.0.mlo issue-meta-0.0.log \
  issue-meta-1.mli issue-meta-1.0.mlo issue-meta-1.0.log \
  issue-meta-2.mli issue-meta-2.0.mlo issue-meta-2.0.log \
  issue-meta-3.mli issue-meta-3.0.mlo issue-meta-3.0.log \
  issue-meta-4.mli issue-meta-4.0.mlo issue-meta-4.0.log \
  issue-meta-5.mli issue-meta-5.0.mlo issue-meta-5.0.log \
  issue-meta-6.mli issue-meta-6.0.mlo issue-meta-6.0.log \
  issue-induction.mli issue-induction.0.mlo issue-induction.0.log \
  issue-induction-2.mli issue-induction-2.0.mlo issue-induction-2.0.log \
  TS1.mli TS1.0.mlo TS1.0.log \
  issue-term.mli issue-term.0.mlo issue-term.0.log \
  issue-gen-spec.mli issue-gen-spec.0.mlo issue-gen-spec.0.log \
  issue-spec.mli issue-spec.0.mlo issue-spec.0.log \
  LLTtoLL3.mli LLTtoLL3.0.mlo LLTtoLL3.0.log \
  test-SM.mli test-SM.0.mlo test-SM.0.log \
  sample-0.mli sample-0.0.mlo sample-0.0.log

TEST_EXTENSIONS = .mli

MLI_LOG_COMPILER = $(srcdir)/mli-test
AM_MLI_LOG_FLAGS = $(abs_top_builddir) $(top_srcdir) 


#tpass_SOURCES = tpass.cc
#tfail_SOURCES = tfail.cc
#tskip_SOURCES = tskip.cc
#terror_SOURCES = terror.cc
#txpass_SOURCES = txpass.cc
#txfail_SOURCES = txfail.cc


SUBDIRS = . 

AM_CXXFLAGS = -std=c++26

clean:
	rm -f *.1.{mlo,log}


# check_PROGRAMS = tpass tfail tskip terror txpass txfail

TESTS = issue-meta-0.mli issue-meta-1.mli issue-meta-2.mli \
  issue-meta-3.mli issue-meta-4.mli issue-meta-5.mli \
  issue-meta-6.mli issue-induction.mli issue-induction-2.mli TS1.mli \
  issue-term.mli issue-gen-spec.mli issue-spec.mli LLTtoLL3.mli test-SM.mli sample-0.mli

# $(check_PROGRAMS)

# XFAIL_TESTS = issue-induction.mli # txpass txfail

