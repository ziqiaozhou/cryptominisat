include_directories(
    ${PROJECT_SOURCE_DIR}
)

include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(${CMAKE_CURRENT_BINARY_DIR}/../include)
if(Boost_FOUND)
	include_directories(${Boost_INCLUDE_DIRS})
endif()
find_package(OpenMP)
if (OPENMP_FOUND)
	set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
	set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()
include_directories(${CMAKE_CURRENT_BINARY_DIR})
set(cryptoms_lib_link_libs "")
set(cryptoms_exec_link_libs
    cryptominisat5
    ${Boost_LIBRARIES}
)
IF (ZLIB_FOUND)
    SET(cryptoms_exec_link_libs ${cryptoms_exec_link_libs} ${ZLIB_LIBRARY})
ENDIF()
add_executable(count
			${PROJECT_SOURCE_DIR}/src/main.cpp
      ${PROJECT_SOURCE_DIR}/src/main_common.cpp
			${PROJECT_SOURCE_DIR}/src/signalcode.cpp
			 count.cpp
       count_main.cpp
       component.cpp
			)
add_executable(sampler
      ${PROJECT_SOURCE_DIR}/src/main.cpp
      ${PROJECT_SOURCE_DIR}/src/main_common.cpp
      ${PROJECT_SOURCE_DIR}/src/signalcode.cpp
      sampler.cpp
      count.cpp
      component.cpp
      )
set(cryptoms_lib_link_libs "")
	target_link_libraries(count
		${cryptoms_exec_link_libs}
		)
	install(TARGETS count
		RUNTIME DESTINATION bin
		)
	SET(CPACK_PACKAGE_EXECUTABLES "count")
  set(cryptoms_lib_link_libs "")
  	target_link_libraries(sampler
  		${cryptoms_exec_link_libs}
  		)
  	install(TARGETS sampler
  		RUNTIME DESTINATION bin
  		)
  	SET(CPACK_PACKAGE_EXECUTABLES "sampler")
