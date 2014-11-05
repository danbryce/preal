################################################################
# GIT HASH
################################################################
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file("${PREAL_SOURCE_DIR}/util/git_sha1.cpp.in" "${PREAL_BINARY_DIR}/git_sha1.cpp" @ONLY)
add_library(util
  "${PREAL_BINARY_DIR}/git_sha1.cpp"
  "${PREAL_SOURCE_DIR}/util/git_sha1.h"
  )
target_link_libraries(util glog)
