% A LaTeX template for MSc Thesis submissions to 
% Politecnico di Milano (PoliMi) - School of Industrial and Information Engineering
%
% P. F. Antonietti, S. Bonetti, A. Gruttadauria, G. Mescolini, A. Zingaro
%
% Last Revision: October 2021
%
% Copyright 2021 Politecnico di Milano, Italy. Inc. All rights reserved

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{TitlePage/Configuration_Files/PoliMi3i_thesis}[2021/6/30 PoliMi3i thesis submission class]
\ProcessOptions\relax

%--------------------------------------------------------------------------
%	HANDLING THE STYLE OF THE THESIS
%--------------------------------------------------------------------------
\LoadClass[12pt, twoside]{article} % 12 pt font, two-sided book style
\RequirePackage[a4paper, includehead, headheight=0.6cm, inner=3.0cm ,outer=2.0cm, top=2.5cm, bottom=2.5cm]{geometry}

\RequirePackage[bf, font=onehalfspacing]{caption} % caption: FIG in bold, 1.5 line spacing in figure and table captions
\newcommand{\thesisspacing}{\onehalfspacing}

%------------------------------------------------------------------------
%	BUILDING THE TITLE PAGE
%------------------------------------------------------------------------

% Define new command: adding background picture (halo) on bottom left (used for empty pages)
\newcommand\BackgroundPic{
	\put(-150,-200){%
		\parbox[b][\paperheight]{\paperwidth}{%
			\vfill
			\centering
			\transparent{0.4}
			\includegraphics[width=0.85\paperwidth]{TitlePage/Images/raggiera_polimi.eps}
			\vfill
}}}

% Define new command: adding background picture (halo) on top right (used for cover page)
\newcommand\BackgroundPicTR{% Adding background picture on top right 
	\put(200,330){%
		\parbox[b][\paperheight]{\paperwidth}{%
			\vfill
			\centering
			\transparent{0.4}
			\includegraphics[width=0.70\paperwidth]{TitlePage/Images/raggiera_polimi.eps}
			\vfill
}}}

\RequirePackage{xkeyval} % Handling keyword options.

% Define keys for title pages
\newif\if@cosupervisorexist\@cosupervisorexistfalse
\define@key[OIST]{title}{title}{\def\thesistitle{#1}}
\define@key[OIST]{title}{course}{\def\course{#1}}
\define@key[OIST]{title}{name}{\def\name{#1}}
\define@key[OIST]{title}{advisor}{\def\advisor{#1}}
\define@key[OIST]{title}{coadvisor}{\def\coadvisor{#1}\@cosupervisorexisttrue}
\define@key[OIST]{title}{academicyear}{\def\academicyear{#1}}
\define@key[OIST]{title}{course}{\def\course{#1}}

\providecommand{\puttitle}{}
\renewcommand{\puttitle}[1]{
	\@puttitle{}{#1}
}

\providecommand{\@puttitle}{}
\renewcommand{\@puttitle}[2]{%
	\setkeys[OIST]{title}{#2}

	\begin{titlepage}
		\AddToShipoutPicture*{\BackgroundPicTR}
			\vfill
			%\begin{minipage}{0.95\textwidth}
			\begin{minipage}{0.95\textwidth}
            \includegraphics[trim={1.2cm 0 0 0},clip, width=0.7\textwidth]{TitlePage/Images/02_ING_IND_INFORMAZIONE_COL_POSITIVO.eps}
            \hfill
            \\
			\vspace{2.5cm}
			\\
			{{\color{bluepoli} \singlespacing \huge \bfseries \thesistitle \par}}	
			\vspace{1.5cm}
			{\color{bluepoli} \bfseries \large{\textsc{\course}}\par}
			\vspace{1.5 cm}
			{Authors: \bfseries{\name}}
			\end{minipage}
			\\
			\vspace*{\fill}
			\\
			\begin{minipage}{0.85\textwidth}
			\normalsize{
			Advisor: {\advisor}
			\\
			Co-advisors: {\coadvisor}
			\\
			Academic Year: {\academicyear}
			}
			\end{minipage}
	\end{titlepage}
}

\newcommand\blankpage{%
    \null
    \AddToShipoutPicture*{\BackgroundPic}
    \thispagestyle{empty}%
    \addtocounter{page}{-1}%
    \newpage
}