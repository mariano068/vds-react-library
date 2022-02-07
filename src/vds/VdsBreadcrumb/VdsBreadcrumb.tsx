import { Breadcrumbs, createTheme, styled, ThemeProvider } from '@mui/material';
import React from 'react';
import { IoMdArrowDropright } from 'react-icons/io';
import '../assets/index.css';

//#region StyledComponents
const theme = createTheme({
  components: {
    //#region definizione delle proprietà di default del breadcrumb
    MuiBreadcrumbs: {
      defaultProps: {
        separator: (
          <IoMdArrowDropright style={{ fontSize: '10px', color: '#005075', width: '32px' }} />
        ),
        maxItems: 10
      }
    }
    //#endregion
  }
})

const StyledBreadcrumb = styled(Breadcrumbs)({
  //#region overflow dello stile di eventuali link
  '.MuiLink-root': {
    letterSpacing: '0',
    fontFamily: 'Cairo, sans-serif',
    fontSize: '14px',
    cursor: 'pointer',
    fontWeight: 400,
    color: '#0090D1',
    textDecoration: 'none'
  },
  '.MuiLink-root:hover': {
    color: '#00C3EA'
  },
  //#endregion
  //#region overflow dello stile di eventuali componenti typography
  '.MuiTypography-body1': {
    letterSpacing: '0',
    fontFamily: 'Cairo, sans-serif',
    fontSize: '14px',
    fontWeight: 700,
    color: '#005075'
  },
  //#endregion
  //#region overflow dello stile dei componenti 'li' utilizzati come container per le icone separatrici 
  '.MuiBreadcrumbs-separator': {
    margin: 0
  }
  //#endregion
})
//#endregion

export const VdsBreadcrumb: React.FC = ({ children }) => {
  return (
    <ThemeProvider theme={theme}>
      <StyledBreadcrumb>{children}</StyledBreadcrumb>
    </ThemeProvider>
  )
}
