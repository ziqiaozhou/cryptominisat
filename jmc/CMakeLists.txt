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
    libcryptominisat5
    ${Boost_LIBRARIES}
)
IF (ZLIB_FOUND)
    SET(cryptoms_exec_link_libs ${cryptoms_exec_link_libs} ${ZLIB_LIBRARY})
ENDIF()
add_executable(jmc
			${PROJECT_SOURCE_DIR}/src/main.cpp
			${PROJECT_SOURCE_DIR}/src/signalcode.cpp
			 jmc.cpp
			)
set(cryptoms_lib_link_libs "")
	target_link_libraries(jmc
		${cryptoms_exec_link_libs}
		)
	install(TARGETS jmc
		RUNTIME DESTINATION bin
		)
	SET(CPACK_PACKAGE_EXECUTABLES "jmc")

