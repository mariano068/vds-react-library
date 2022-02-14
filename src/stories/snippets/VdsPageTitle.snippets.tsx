import { Link, Typography } from '@mui/material'
import * as React from 'react'
import { VdsBreadcrumb } from '../../vds/VdsBreadcrumb/VdsBreadcrumb'
import { VdsPageTitle } from '../../vds/VdsPageTitle/VdsPageTitle'
import { convert } from '../utils'

//#region Default Example
export const pageTitle_default_example_snippet = convert(`
import React from 'react';
import { VdsPageTitle } from 'vds-components';

export default () => {

    return (
      <VdsPageTitle title="PAGE TITLE" />
    );
}
`)
export const PageTitle_Default_Example = () => {

  return (
    <VdsPageTitle title="PAGE TITLE" />
  )
}
//#endregion

//#region PageTitle WithDescription
export const pageTitle_withDescription_example_snippet = convert(`
import React from 'react';
import { VdsPageTitle } from 'vds-components';

export default () => {

  const handleBackEvent = () => console.dir('click');

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content="Page description or explanation text"
    />
  );
}
`)
export const PageTitle_WithDescription_Example = () => {

  const handleBackEvent = () => console.dir('click');

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content="Page description or explanation text"
    />
  )
}
//#endregion

//#region PageTitle WithDescription
export const pageTitle_withoutBreadcrumb_example_snippet = convert(`
import React from 'react';
import { Link, Typography } from '@mui/material';
import { VdsPageTitle, VdsBreadcrumb } from 'vds-components';

export default () => {

  const handleBackEvent = () => console.dir('click');
  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content={
        <VdsBreadcrumb>
          <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 4</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 5</Link>
          <Typography>Text 1</Typography>
        </VdsBreadcrumb>
      }
    />
  )
}
`)
export const PageTitle_WithoutBreadcrumb_Example = () => {

  const handleBackEvent = () => console.dir('click');
  const onClickHandler: React.MouseEventHandler<HTMLAnchorElement> = (ev) => console.dir(ev);

  return (
    <VdsPageTitle
      title="PAGE TITLE"
      historyBackEvent={handleBackEvent}
      content={
        <VdsBreadcrumb>
          <Link onClick={onClickHandler}>Breadcrumb link 1</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 2</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 3</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 4</Link>
          <Link onClick={onClickHandler}>Breadcrumb link 5</Link>
          <Typography>Text 1</Typography>
        </VdsBreadcrumb>
      }
    />
  )
}
//#endregion
